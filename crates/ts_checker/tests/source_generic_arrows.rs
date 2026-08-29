use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeError,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, TypeNodeUnavailable,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(8_200);
const IMPORTER: FileId = FileId::new(8_201);
const PROVIDER: FileId = FileId::new(8_202);
const TYPES: FileId = FileId::new(8_203);
const ARRAY_LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}\n";
const IMPORTED_TYPES: &str =
    "export interface Shape { id: number } export interface Cell<T> { value: T }";

struct TypeParameterParts {
    declaration: NodeRef,
    name: NodeRef,
    constraint: Option<NodeRef>,
    default: Option<NodeRef>,
}

struct ParameterParts {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct ArrowParts {
    declaration: NodeRef,
    value_declaration: NodeRef,
    value_name: Option<NodeRef>,
    type_parameters: Vec<TypeParameterParts>,
    parameters: Vec<ParameterParts>,
    return_annotation: NodeRef,
    body_expression: NodeRef,
}

impl ArrowParts {
    fn annotations(&self) -> Vec<NodeRef> {
        self.type_parameters
            .iter()
            .flat_map(|parameter| [parameter.constraint, parameter.default])
            .flatten()
            .chain(self.parameters.iter().map(|parameter| parameter.annotation))
            .chain([self.return_annotation])
            .collect()
    }
}

#[derive(Debug, Eq, PartialEq)]
struct TypeParameterState {
    symbol: SemanticSymbolId,
    type_: TypeId,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
    base_constraint: Option<TypeId>,
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowSnapshot {
    owner: SemanticSymbolId,
    value_owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    type_parameters: Vec<TypeParameterState>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    return_type: TypeId,
    body_type: TypeId,
    annotations: Vec<(NodeRef, TypeId)>,
}

#[derive(Clone, Copy)]
enum DiagnosticSite {
    Constraint,
    Default,
    Body,
}

fn options() -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
        strict_function_types: true,
        ..CanonicalCheckerOptions::default()
    }
}

fn facts(name: &str, module: CanonicalModuleState) -> CanonicalSourceFileFacts {
    CanonicalSourceFileFacts::new(
        EscapedName::source(name),
        CanonicalSourceLanguage::TypeScript,
        false,
        module,
    )
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            facts("\"/project/arrows.ts\"", CanonicalModuleState::Script),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(binder.finish(), vec![(FILE, &parsed.arena)], options()).unwrap()
}

fn arrow_parts(parsed: &ParseResult, file: FileId) -> ArrowParts {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
    let arrows = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::ArrowFunction(arrow) = &record.data else {
                return None;
            };
            Some((node, record, arrow))
        })
        .collect::<Vec<_>>();
    let [(node, record, arrow)] = arrows.as_slice() else {
        panic!("each source must contain one actual ArrowFunction")
    };
    let value_declaration = node_ref(record.parent.unwrap());
    let value_name = match &parsed.arena.get(value_declaration.node).unwrap().data {
        NodeData::VariableDeclaration(variable) => {
            assert_eq!(variable.initializer, Some(*node));
            Some(node_ref(variable.name))
        }
        NodeData::ExportAssignment(export) => {
            assert!(!export.is_export_equals);
            assert_eq!(export.expression, *node);
            None
        }
        _ => panic!("the arrow must belong to a variable or direct default export"),
    };
    let body_expression = match &parsed.arena.get(arrow.body).unwrap().data {
        NodeData::Block(block) => {
            let [statement] = block.statements.nodes.as_slice() else {
                panic!("the block control must retain one return statement")
            };
            let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data
            else {
                panic!("expected the existing single-return body")
            };
            node_ref(returned.expression.unwrap())
        }
        _ => node_ref(arrow.body),
    };
    ArrowParts {
        declaration: node_ref(*node),
        value_declaration,
        value_name,
        type_parameters: arrow
            .type_parameters
            .as_ref()
            .into_iter()
            .flat_map(|parameters| &parameters.nodes)
            .map(|&node| {
                let NodeData::TypeParameterDeclaration(parameter) =
                    &parsed.arena.get(node).unwrap().data
                else {
                    panic!("expected a type parameter")
                };
                TypeParameterParts {
                    declaration: node_ref(node),
                    name: node_ref(parameter.name),
                    constraint: parameter.constraint.map(node_ref),
                    default: parameter.default_type.map(node_ref),
                }
            })
            .collect(),
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .map(|&node| {
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(node).unwrap().data
                else {
                    panic!("expected a typed identifier parameter")
                };
                ParameterParts {
                    declaration: node_ref(node),
                    name: node_ref(parameter.name),
                    annotation: node_ref(parameter.type_.unwrap()),
                }
            })
            .collect(),
        return_annotation: node_ref(arrow.type_.unwrap()),
        body_expression,
    }
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

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

fn signature(context: &CanonicalCheckerContext<'_>, arrow: &ArrowParts) -> SignatureId {
    context
        .store()
        .signature_links(arrow.declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn snapshot(context: &mut CanonicalCheckerContext<'_>, arrow: &ArrowParts) -> ArrowSnapshot {
    let signature = signature(context, arrow);
    let return_type = context.get_return_type_of_signature(signature).unwrap();
    snapshot_with_return_type(context, arrow, return_type)
}

#[allow(clippy::too_many_lines)] // Keep both owners and the complete signature graph together.
fn snapshot_with_return_type(
    context: &mut CanonicalCheckerContext<'_>,
    arrow: &ArrowParts,
    return_type: TypeId,
) -> ArrowSnapshot {
    let owner = symbol(context, arrow.declaration);
    let value_owner = symbol(context, arrow.value_declaration);
    assert_ne!(owner, value_owner);
    let owner_record = context.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[arrow.declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(arrow.declaration));
    let value_record = context.store().symbol(value_owner).unwrap();
    assert_eq!(
        value_record.declarations(),
        Some(&[arrow.value_declaration][..])
    );
    assert_eq!(
        value_record.value_declaration(),
        Some(arrow.value_declaration)
    );
    assert_eq!(
        value_record.flags(),
        if arrow.value_name.is_some() {
            SymbolFlags::BLOCK_SCOPED_VARIABLE
        } else {
            SymbolFlags::PROPERTY
        }
    );
    if arrow.value_name.is_none() {
        let source = context
            .source_file(arrow.declaration.file)
            .unwrap()
            .node_ref();
        let module = symbol(context, source);
        let exports = context.store().symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("default"),
            Some(value_owner)
        );
    }
    let callable = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(value_owner)
            .unwrap()
            .resolved_type,
        Some(callable)
    );
    assert_eq!(
        context.get_type_at_location(arrow.declaration).unwrap(),
        callable
    );
    if let Some(name) = arrow.value_name {
        assert_eq!(context.get_type_at_location(name).unwrap(), callable);
        assert_eq!(
            context.get_symbol_at_location(name).unwrap(),
            Some(value_owner)
        );
    }
    let signature = signature(context, arrow);
    let record = context.store().type_payload(callable).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("expected the arrow's callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    // Checked artifact queries preserve imported annotation ownership.
    let annotations = arrow
        .annotations()
        .into_iter()
        .map(|node| (node, context.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        context
            .get_type_at_location(arrow.return_annotation)
            .unwrap(),
        return_type
    );
    let type_parameters = arrow
        .type_parameters
        .iter()
        .map(|parameter| {
            let symbol = symbol(context, parameter.declaration);
            let type_ = context
                .store()
                .declared_type_links(symbol)
                .unwrap()
                .declared_type
                .unwrap();
            assert_eq!(context.get_type_at_location(parameter.name).unwrap(), type_);
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol)
            );
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(symbol));
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("expected the binder-owned type parameter")
            };
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            TypeParameterState {
                symbol,
                type_,
                constraint: data.constraint,
                default: data.resolved_default_type,
                base_constraint: data.constrained.resolved_base_constraint,
            }
        })
        .collect::<Vec<_>>();
    let parameters = arrow
        .parameters
        .iter()
        .map(|parameter| {
            let symbol = symbol(context, parameter.declaration);
            let type_ = context.get_type_at_location(parameter.annotation).unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
            assert_eq!(context.get_type_at_location(parameter.name).unwrap(), type_);
            (symbol, type_)
        })
        .collect::<Vec<_>>();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(arrow.declaration));
    assert_eq!(
        record.type_parameters(),
        type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>()
    );
    assert_eq!(record.resolved_return_type(), Some(return_type));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let body_type = context.get_type_at_location(arrow.body_expression).unwrap();
    ArrowSnapshot {
        owner,
        value_owner,
        callable,
        signature,
        type_parameters,
        parameters,
        return_type,
        body_type,
        annotations,
    }
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    arrow: &ArrowParts,
    expected: &[(u32, &str, DiagnosticSite)],
) {
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, &(code, message, site)) in diagnostics.iter().zip(expected) {
        let node = match site {
            DiagnosticSite::Constraint => arrow.type_parameters[0].constraint.unwrap(),
            DiagnosticSite::Default => arrow.type_parameters[0].default.unwrap(),
            DiagnosticSite::Body => arrow.body_expression,
        };
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    }
}

fn call_results(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) -> Vec<(NodeRef, TypeId, SignatureId)> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|&(start, _)| start);
    calls
        .into_iter()
        .map(|(_, call)| {
            let type_ = context.get_type_at_location(call).unwrap();
            let signature = context
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            (call, type_, signature)
        })
        .collect()
}

fn check_orders(
    source: &str,
    expected: &[(u32, &str, DiagnosticSite)],
    assert_case: impl Fn(&mut CanonicalCheckerContext<'_>, &ParseResult, &ArrowParts, &ArrowSnapshot),
) {
    let parsed = parse_source_file(source);
    let arrow = arrow_parts(&parsed, FILE);
    let first_queries = std::iter::once(None).chain(arrow.annotations().into_iter().map(Some));
    for first in first_queries {
        let mut context = context(&parsed);
        assert!(!checked(&context, FILE));
        let early = first.map(|node| (node, context.get_type_from_type_node(node).unwrap()));
        assert!(context.store().signature_links(arrow.declaration).is_none());
        assert!(!checked(&context, FILE));
        if expected
            .iter()
            .any(|&(_, _, site)| matches!(site, DiagnosticSite::Body))
        {
            assert!(context.diagnostics().is_empty());
        }
        context.check_source_file(FILE).unwrap();
        assert!(checked(&context, FILE));
        assert_diagnostics(&context, &arrow, expected);
        let cold = snapshot(&mut context, &arrow);
        if let Some(early) = early {
            assert!(cold.annotations.contains(&early));
        }
        assert_case(&mut context, &parsed, &arrow, &cold);
        let calls = call_results(&mut context, &parsed, FILE);
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&mut context, &arrow), cold);
        assert_case(&mut context, &parsed, &arrow, &cold);
        assert_eq!(call_results(&mut context, &parsed, FILE), calls);
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

fn assert_identity(
    context: &mut CanonicalCheckerContext<'_>,
    arrow: &ArrowParts,
    state: &ArrowSnapshot,
) {
    let type_ = state.type_parameters[0].type_;
    assert_eq!(state.parameters[0].1, type_);
    assert_eq!(state.return_type, type_);
    assert_eq!(state.body_type, type_);
    assert_eq!(
        context
            .get_symbol_at_location(arrow.body_expression)
            .unwrap(),
        Some(state.parameters[0].0)
    );
}

#[test]
fn generic_arrow_identity_keeps_owners_and_existing_call_inference() {
    check_orders(
        concat!(
            "const keep = <T>(value: T): T => value;\n",
            "const explicit: number = keep<number>(1);\n",
            "const inferred: 'kept' = keep('kept');\n",
        ),
        &[],
        |context, parsed, arrow, state| {
            assert_identity(context, arrow, state);
            let calls = call_results(context, parsed, FILE);
            assert_eq!(calls.len(), 2);
            assert_eq!(
                calls[0].1,
                context.store().intrinsic_bootstrap().unwrap().number_type
            );
            assert_eq!(
                context.store().type_payload(calls[1].1).unwrap().flags(),
                TypeFlags::STRING_LITERAL
            );
            for (_, _, signature) in calls {
                let record = context.store().signature(signature).unwrap();
                assert_eq!(record.target(), Some(state.signature));
                assert!(record.mapper().is_some());
                assert!(record.type_parameters().is_empty());
            }
        },
    );
}

#[test]
fn generic_arrow_single_return_block_keeps_parameter_identity() {
    check_orders(
        "const keep = <T>(value: T): T => { return value; };",
        &[],
        |context, _, arrow, state| {
            assert_identity(context, arrow, state);
        },
    );
}

#[test]
fn generic_arrow_zero_parameters_keep_the_explicit_return_type() {
    check_orders(
        "const make = <T>(): number => 1;",
        &[],
        |context, _, _, state| {
            assert!(state.parameters.is_empty());
            assert_eq!(state.type_parameters.len(), 1);
            assert_eq!(
                state.return_type,
                context.store().intrinsic_bootstrap().unwrap().number_type
            );
            assert_eq!(
                context
                    .store()
                    .type_payload(state.body_type)
                    .unwrap()
                    .flags(),
                TypeFlags::NUMBER_LITERAL
            );
        },
    );
}

#[test]
fn generic_arrow_interface_annotations_preserve_the_outer_parameter() {
    // This interface control does not replace the existing Box type-alias control.
    check_orders(
        "interface Box<T> { value: T } const keepBox = <T>(value: Box<T>): Box<T> => { return value; };",
        &[],
        |context, parsed, arrow, state| {
            assert_eq!(state.parameters[0].1, state.return_type);
            assert_eq!(state.body_type, state.return_type);
            let interface = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
                })
                .unwrap();
            let target = context
                .get_declared_type_of_symbol(symbol(context, interface))
                .unwrap();
            let TypeData::TypeReference(reference) = context
                .store()
                .type_payload(state.return_type)
                .unwrap()
                .data()
            else {
                panic!("Box<T> must retain its interface reference")
            };
            assert_eq!(reference.object.target, Some(target));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[state.type_parameters[0].type_][..])
            );
            assert_eq!(
                context
                    .get_symbol_at_location(arrow.body_expression)
                    .unwrap(),
                Some(state.parameters[0].0)
            );
        },
    );
}

#[test]
fn generic_arrow_array_constraint_and_default_keep_the_same_array() {
    let source =
        format!("{ARRAY_LIBRARY}const defaults = <T, U extends T[] = T[]>(value: U): U => value;");
    check_orders(&source, &[], |context, _, _, state| {
        let [t, u] = state.type_parameters.as_slice() else {
            panic!("expected ordered T and U")
        };
        assert_ne!(t.type_, u.type_);
        assert_eq!(u.constraint, u.default);
        assert_eq!(state.parameters[0].1, u.type_);
        assert_eq!(state.return_type, u.type_);
        assert_eq!(state.body_type, u.type_);
        let TypeData::TypeReference(reference) = context
            .store()
            .type_payload(u.constraint.unwrap())
            .unwrap()
            .data()
        else {
            panic!("the constraint must use the declared Array target")
        };
        assert_eq!(
            reference.object.target,
            Some(context.global_types().array_type)
        );
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[t.type_][..])
        );
    });
}

#[test]
fn generic_arrow_invalid_body_is_checked_after_return_annotation_demand() {
    check_orders(
        "const bad = <T>(): string => 1;",
        &[(
            2322,
            "Type 'number' is not assignable to type 'string'.",
            DiagnosticSite::Body,
        )],
        |context, _, _, state| {
            assert_eq!(
                state.return_type,
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
            assert_eq!(
                context
                    .store()
                    .type_payload(state.body_type)
                    .unwrap()
                    .flags(),
                TypeFlags::NUMBER_LITERAL
            );
        },
    );
}

#[test]
fn generic_arrow_self_constraint_reports_2313_and_retains_t() {
    check_orders(
        "const circular = <T extends T>(value: T): T => value;",
        &[(
            2313,
            "Type parameter 'T' has a circular constraint.",
            DiagnosticSite::Constraint,
        )],
        |context, _, arrow, state| {
            assert_identity(context, arrow, state);
            let t = &state.type_parameters[0];
            assert_eq!(t.constraint, Some(t.type_));
            assert_eq!(
                t.base_constraint,
                Some(
                    context
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .circular_constraint_type
                )
            );
        },
    );
}

#[test]
fn generic_arrow_invalid_default_reports_2344_and_retains_number() {
    check_orders(
        "const bad = <T extends string = number>(): string => '';",
        &[(
            2344,
            "Type 'number' does not satisfy the constraint 'string'.",
            DiagnosticSite::Default,
        )],
        |context, _, _, state| {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let t = &state.type_parameters[0];
            assert_eq!(t.constraint, Some(bootstrap.string_type));
            assert_eq!(t.base_constraint, Some(bootstrap.string_type));
            assert_eq!(t.default, Some(bootstrap.number_type));
            assert_eq!(state.return_type, bootstrap.string_type);
        },
    );
}

fn module_context<'arena>(
    importer: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    module_context_with_types(importer, provider, None)
}

fn module_context_with_types<'arena>(
    importer: &'arena ParseResult,
    provider: &'arena ParseResult,
    types: Option<&'arena ParseResult>,
) -> CanonicalCheckerContext<'arena> {
    let mut files = vec![
        (IMPORTER, importer, "\"/project/importer.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
    ];
    if let Some(types) = types {
        files.push((TYPES, types, "\"/project/types.ts\""));
    }
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, name) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                facts(name, CanonicalModuleState::External),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut edges = vec![(IMPORTER, importer, PROVIDER)];
    if types.is_some() {
        edges.push((PROVIDER, provider, TYPES));
    }
    let resolutions = edges.into_iter().map(|(file, parsed, target)| {
        let specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    import.module_specifier,
                ))
            })
            .collect::<Vec<_>>();
        let [specifier] = specifiers.as_slice() else {
            panic!("expected one exact module edge")
        };
        CanonicalModuleResolutionEntry::resolved(
            *specifier,
            CanonicalResolvedModuleInput::new(
                target,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        options(),
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn default_import_clause(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportClause(clause) = &record.data else {
                return None;
            };
            clause
                .name
                .map(|_| NodeRef::new(parsed.arena.id(), IMPORTER, node))
        })
        .unwrap()
}

#[allow(clippy::too_many_lines)] // This test controls source order and preserves the complete import graph.
fn check_default_import(provider_source: &str, importer_source: &str, generic: bool) {
    let provider = parse_source_file(provider_source);
    let importer = parse_source_file(importer_source);
    let arrow = arrow_parts(&provider, PROVIDER);
    let clause = default_import_clause(&importer);
    for provider_first in [false, true] {
        let mut context = module_context(&importer, &provider);
        assert_eq!(context.file_order(), [IMPORTER, PROVIDER]);
        let owner = symbol(&context, arrow.declaration);
        let exported = symbol(&context, arrow.value_declaration);
        let alias = symbol(&context, clause);
        assert_ne!(alias, exported);
        assert_ne!(exported, owner);
        assert_ne!(alias, owner);
        assert_eq!(
            context.store().symbol(owner).unwrap().flags(),
            SymbolFlags::FUNCTION
        );
        assert_eq!(
            context.store().symbol(exported).unwrap().flags(),
            SymbolFlags::PROPERTY
        );
        assert_eq!(
            context.store().symbol(alias).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        assert!(!checked(&context, PROVIDER));
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(IMPORTER).unwrap();
        assert!(checked(&context, IMPORTER));
        assert_eq!(checked(&context, PROVIDER), provider_first);
        if !provider_first {
            assert!(
                context
                    .store()
                    .type_node_links(arrow.body_expression)
                    .is_none()
            );
        }
        let links = context.store().alias_symbol_links(alias).unwrap();
        assert_eq!(links.immediate_target, Some(exported));
        assert_eq!(links.alias_target, AliasTargetState::Resolved(exported));
        assert_eq!(links.type_only_declaration, None);
        let callable = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        for symbol in [exported, alias] {
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(callable)
            );
        }
        let definition_signature = signature(&context, &arrow);
        let type_parameters = context
            .store()
            .signature(definition_signature)
            .unwrap()
            .type_parameters()
            .to_vec();
        assert_eq!(type_parameters.len(), usize::from(generic));
        let returned = context
            .get_return_type_of_signature(definition_signature)
            .unwrap();
        if generic {
            assert_eq!(returned, type_parameters[0]);
            assert_eq!(
                context
                    .store()
                    .type_payload(type_parameters[0])
                    .unwrap()
                    .symbol(),
                Some(symbol(&context, arrow.type_parameters[0].declaration))
            );
        } else {
            assert_eq!(
                returned,
                context.store().intrinsic_bootstrap().unwrap().number_type
            );
        }
        // A return query does not certify the provider's body.
        assert_eq!(checked(&context, PROVIDER), provider_first);
        let calls = call_results(&mut context, &importer, IMPORTER);
        assert_eq!(calls.len(), if generic { 2 } else { 1 });
        assert_eq!(
            calls[0].1,
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        for &(_, _, selected) in &calls {
            let record = context.store().signature(selected).unwrap();
            if generic {
                assert_eq!(record.target(), Some(definition_signature));
                assert!(record.mapper().is_some());
            } else {
                assert_eq!(selected, definition_signature);
            }
        }
        assert_eq!(checked(&context, PROVIDER), provider_first);
        context.check_source_file(PROVIDER).unwrap();
        assert!(checked(&context, PROVIDER));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let definition = snapshot(&mut context, &arrow);
        assert_eq!(definition.callable, callable);
        assert_eq!(definition.signature, definition_signature);
        assert_eq!(
            definition
                .type_parameters
                .iter()
                .map(|parameter| parameter.type_)
                .collect::<Vec<_>>(),
            type_parameters
        );
        assert_eq!(definition.return_type, returned);
        assert_eq!(definition.body_type, returned);
        assert_eq!(
            context
                .get_symbol_at_location(arrow.body_expression)
                .unwrap(),
            Some(definition.parameters[0].0)
        );
        let aliases = context.store().alias_symbol_links(alias).cloned();
        let before = counts(&context);
        context.recheck_source_file(IMPORTER).unwrap();
        context.recheck_source_file(PROVIDER).unwrap();
        assert_eq!(snapshot(&mut context, &arrow), definition);
        assert_eq!(call_results(&mut context, &importer, IMPORTER), calls);
        assert_eq!(context.store().alias_symbol_links(alias).cloned(), aliases);
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn default_nongeneric_arrow_import_keeps_export_and_callable_owners_separate() {
    check_default_import(
        "export default (value: number): number => value;",
        "import keep from './provider'; const result: number = keep(1);",
        false,
    );
}

#[test]
fn default_generic_arrow_import_keeps_definition_ids_in_both_source_orders() {
    check_default_import(
        "export default <T>(value: T): T => value;",
        concat!(
            "import keep from './provider';\n",
            "const explicit: number = keep<number>(1);\n",
            "const inferred: 'kept' = keep('kept');\n",
        ),
        true,
    );
}

#[test]
fn importer_first_generic_default_return_demand_does_not_check_the_provider_body() {
    let provider = parse_source_file("export default <T>(): string => 1;");
    let importer =
        parse_source_file("import make from './provider'; const text: string = make<number>();");
    let arrow = arrow_parts(&provider, PROVIDER);
    let mut context = module_context(&importer, &provider);
    context.check_source_file(IMPORTER).unwrap();
    assert!(checked(&context, IMPORTER));
    assert!(!checked(&context, PROVIDER));
    assert!(context.diagnostics().is_empty());
    assert!(
        context
            .store()
            .type_node_links(arrow.body_expression)
            .is_none()
    );
    let signature = signature(&context, &arrow);
    let returned = context.get_return_type_of_signature(signature).unwrap();
    assert_eq!(
        returned,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert!(!checked(&context, PROVIDER));
    assert!(context.diagnostics().is_empty());
    context.check_source_file(PROVIDER).unwrap();
    assert!(checked(&context, PROVIDER));
    assert_diagnostics(
        &context,
        &arrow,
        &[(
            2322,
            "Type 'number' is not assignable to type 'string'.",
            DiagnosticSite::Body,
        )],
    );
    let definition = snapshot(&mut context, &arrow);
    assert_eq!(definition.signature, signature);
    assert_eq!(definition.return_type, returned);
    let calls = call_results(&mut context, &importer, IMPORTER);
    assert_eq!(calls[0].1, returned);
    let before = counts(&context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(PROVIDER).unwrap();
    context.recheck_source_file(IMPORTER).unwrap();
    assert_eq!(snapshot(&mut context, &arrow), definition);
    assert_eq!(call_results(&mut context, &importer, IMPORTER), calls);
    assert_eq!(counts(&context), before);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[derive(Clone, Copy)]
enum ImportedAnnotation {
    Shape,
    CellParameter,
    CellShape,
}

fn interface_declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
}

#[allow(clippy::too_many_lines)] // Keep node, symbol, signature, and source cache checks together.
fn assert_imported_return_query_unavailable(
    context: &mut CanonicalCheckerContext<'_>,
    arrow: &ArrowParts,
    alias_declaration: NodeRef,
) {
    let signature = signature(context, arrow);
    let alias = symbol(context, alias_declaration);
    let mut nodes = Vec::new();
    let mut symbols = Vec::new();
    for &file in context.file_order() {
        let (arena, bound) = context.file(file).unwrap();
        for (node, _) in arena.iter() {
            let node = NodeRef::new(arena.id(), file, node);
            nodes.push(node);
            if let Some(symbol) = bound.symbol(node) {
                let symbol = context.store().get_merged_symbol(symbol).unwrap();
                if !symbols.contains(&symbol) {
                    symbols.push(symbol);
                }
            }
        }
    }
    let cache_state = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        let signature_record = store.signature(signature).unwrap();
        (
            (
                signature_record.declaration(),
                signature_record.type_parameters().to_vec(),
                signature_record.parameters().to_vec(),
                signature_record.this_parameter(),
                signature_record.resolved_return_type(),
                signature_record.resolved_type_predicate(),
                signature_record.target(),
                signature_record.mapper(),
            ),
            nodes
                .iter()
                .map(|&node| {
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            symbols
                .iter()
                .map(|&symbol| {
                    (
                        symbol,
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
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
        )
    };
    let before = cache_state(context);
    let before_counts = counts(context);
    let diagnostics = context.diagnostics().clone();
    let provider_checked = checked(context, PROVIDER);
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Err(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::ImportAliasTypeReference {
                node: arrow.parameters[0].annotation,
                alias,
            },
        )),
    );
    assert_eq!(cache_state(context), before);
    assert_eq!(counts(context), before_counts);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(checked(context, PROVIDER), provider_checked);
}

#[allow(clippy::too_many_lines)] // Keep imported ownership, deferred body checking, and replay together.
fn check_imported_annotation(provider_source: &str, annotation: ImportedAnnotation) {
    let types = parse_source_file(IMPORTED_TYPES);
    let provider = parse_source_file(provider_source);
    let importer = parse_source_file("import keep from './provider'; const copy = keep;");
    let arrow = arrow_parts(&provider, PROVIDER);
    let clause = default_import_clause(&importer);
    let copy = importer
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            Some(NodeRef::new(importer.arena.id(), IMPORTER, variable.name))
        })
        .unwrap();
    let shape = interface_declaration(&types, TYPES, "Shape");
    let cell = interface_declaration(&types, TYPES, "Cell");
    let root_alias_name = match annotation {
        ImportedAnnotation::Shape => "Shape",
        ImportedAnnotation::CellParameter | ImportedAnnotation::CellShape => "Cell",
    };
    let root_alias = provider
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(specifier) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &provider.arena.get(specifier.name)?.data else {
                return None;
            };
            (name.text == root_alias_name).then_some(NodeRef::new(
                provider.arena.id(),
                PROVIDER,
                node,
            ))
        })
        .unwrap();
    for provider_first in [false, true] {
        let mut context = module_context_with_types(&importer, &provider, Some(&types));
        assert_eq!(context.file_order(), [IMPORTER, PROVIDER, TYPES]);
        let owner = symbol(&context, arrow.declaration);
        let exported = symbol(&context, arrow.value_declaration);
        let alias = symbol(&context, clause);
        assert_ne!(owner, exported);
        assert_ne!(owner, alias);
        assert_ne!(alias, exported);
        assert_eq!(
            context.store().symbol(owner).unwrap().flags(),
            SymbolFlags::FUNCTION
        );
        assert_eq!(
            context.store().symbol(exported).unwrap().flags(),
            SymbolFlags::PROPERTY
        );
        assert_eq!(
            context.store().symbol(alias).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(IMPORTER).unwrap();
        assert!(checked(&context, IMPORTER));
        assert_eq!(checked(&context, PROVIDER), provider_first);
        if !provider_first {
            assert!(
                context
                    .store()
                    .type_node_links(arrow.body_expression)
                    .is_none()
            );
            assert!(context.store().type_node_links(arrow.declaration).is_none());
        }
        let callable = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        for symbol in [exported, alias] {
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(callable)
            );
        }
        assert_eq!(context.get_type_at_location(copy).unwrap(), callable);
        let aliases = context.store().alias_symbol_links(alias).cloned().unwrap();
        assert_eq!(aliases.immediate_target, Some(exported));
        assert_eq!(aliases.alias_target, AliasTargetState::Resolved(exported));
        let definition_signature = signature(&context, &arrow);
        let record = context.store().signature(definition_signature).unwrap();
        let [t] = record.type_parameters() else {
            panic!("expected the arrow's one type parameter")
        };
        let t = *t;
        let [parameter] = record.parameters() else {
            panic!("expected one typed value parameter")
        };
        let parameter = *parameter;
        // Import demand resolved this return with the provider's annotation capabilities.
        let returned = record.resolved_return_type().unwrap();
        assert_imported_return_query_unavailable(&mut context, &arrow, root_alias);
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(returned)
        );
        assert_ne!(returned, t);
        assert_eq!(
            context.store().type_payload(t).unwrap().symbol(),
            Some(symbol(&context, arrow.type_parameters[0].declaration))
        );
        assert_eq!(checked(&context, PROVIDER), provider_first);
        assert!(context.diagnostics().is_empty());
        if !provider_first {
            assert!(
                context
                    .store()
                    .type_node_links(arrow.body_expression)
                    .is_none()
            );
        }

        let shape_symbol = symbol(&context, shape);
        let cell_symbol = symbol(&context, cell);
        let shape_type = context.get_declared_type_of_symbol(shape_symbol).unwrap();
        let cell_type = context.get_declared_type_of_symbol(cell_symbol).unwrap();
        match annotation {
            ImportedAnnotation::Shape => assert_eq!(returned, shape_type),
            ImportedAnnotation::CellParameter | ImportedAnnotation::CellShape => {
                let TypeData::TypeReference(reference) =
                    context.store().type_payload(returned).unwrap().data()
                else {
                    panic!("the imported Cell must remain a real interface reference")
                };
                assert_eq!(reference.object.target, Some(cell_type));
                let argument = match annotation {
                    ImportedAnnotation::CellParameter => t,
                    ImportedAnnotation::CellShape => shape_type,
                    ImportedAnnotation::Shape => unreachable!(),
                };
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some(&[argument][..])
                );
            }
        }
        let imported_aliases = provider
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::ImportSpecifier(specifier) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &provider.arena.get(specifier.name)?.data else {
                    return None;
                };
                let target = match name.text.as_str() {
                    "Shape" => shape_symbol,
                    "Cell" => cell_symbol,
                    _ => panic!("unexpected imported annotation name"),
                };
                let alias = symbol(&context, NodeRef::new(provider.arena.id(), PROVIDER, node));
                let links = context.store().alias_symbol_links(alias).cloned().unwrap();
                assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
                Some((alias, links))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            imported_aliases.len(),
            if matches!(annotation, ImportedAnnotation::CellShape) {
                2
            } else {
                1
            }
        );
        context.check_source_file(PROVIDER).unwrap();
        context.check_source_file(TYPES).unwrap();
        assert!(checked(&context, PROVIDER));
        let definition = snapshot_with_return_type(&mut context, &arrow, returned);
        assert_eq!(definition.callable, callable);
        assert_eq!(definition.signature, definition_signature);
        assert_eq!(definition.type_parameters[0].type_, t);
        assert_eq!(definition.parameters, [(parameter, returned)]);
        assert_eq!(definition.return_type, returned);
        assert_eq!(definition.body_type, returned);
        assert!(context.diagnostics().is_empty());
        assert_imported_return_query_unavailable(&mut context, &arrow, root_alias);
        let before = counts(&context);
        context.recheck_source_file(IMPORTER).unwrap();
        context.recheck_source_file(PROVIDER).unwrap();
        context.recheck_source_file(TYPES).unwrap();
        assert_eq!(
            snapshot_with_return_type(&mut context, &arrow, returned),
            definition
        );
        assert_imported_return_query_unavailable(&mut context, &arrow, root_alias);
        assert_eq!(context.get_type_at_location(copy).unwrap(), callable);
        assert_eq!(context.store().alias_symbol_links(alias), Some(&aliases));
        for (alias, links) in imported_aliases {
            assert_eq!(context.store().alias_symbol_links(alias), Some(&links));
        }
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn default_generic_arrow_imports_nongeneric_shape_without_checking_its_body() {
    check_imported_annotation(
        "import type { Shape } from './types'; export default <T>(value: Shape): Shape => value;",
        ImportedAnnotation::Shape,
    );
}

#[test]
fn default_generic_arrow_imports_cell_with_its_own_type_parameter() {
    check_imported_annotation(
        "import type { Cell } from './types'; export default <T>(value: Cell<T>): Cell<T> => value;",
        ImportedAnnotation::CellParameter,
    );
}

#[test]
fn default_generic_arrow_imports_nested_shape_arguments() {
    check_imported_annotation(
        "import type { Cell, Shape } from './types'; export default <T>(value: Cell<Shape>): Cell<Shape> => value;",
        ImportedAnnotation::CellShape,
    );
}
