use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, AssertionLinks, CanonicalCheckerContext,
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, SignatureLinks, SourceCheckError, SourceFileLinks,
    SourceSyntaxRole, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_801);
const PROVIDER: FileId = FileId::new(9_802);
const CONFIG_PROVIDER: &str = concat!(
    "export interface ViteUserConfig { value: number; } ",
    "export function defineConfig(config: { value: number }): { value: number } { return config; }",
);

#[derive(Clone, Copy)]
struct AssertionParts {
    expression: NodeRef,
    operand: NodeRef,
    target: NodeRef,
}

impl AssertionParts {
    fn nodes(self) -> [NodeRef; 3] {
        [self.expression, self.operand, self.target]
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 4],
    source: SourceFileLinks,
    types: Vec<Option<TypeNodeLinks>>,
    assertions: Vec<Option<AssertionLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    aliases: Vec<Option<AliasSymbolLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn context<'arena>(
    source: &'arena ParseResult,
    module: CanonicalModuleState,
    provider: Option<&'arena ParseResult>,
) -> CanonicalCheckerContext<'arena> {
    let mut files = vec![(FILE, source, "\"/project/config.ts\"", module)];
    if let Some(provider) = provider {
        files.push((
            PROVIDER,
            provider,
            "\"/project/provider.ts\"",
            CanonicalModuleState::External,
        ));
    }
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, module) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = provider
        .map(|_| {
            let specifier = source
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::ImportDeclaration(import) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(
                        source.arena.id(),
                        FILE,
                        import.module_specifier,
                    ))
                })
                .expect("the config has one import declaration");
            CanonicalModuleResolutionEntry::resolved(
                specifier,
                CanonicalResolvedModuleInput::new(
                    PROVIDER,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        })
        .into_iter();
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn assertion_parts(parsed: &ParseResult, kind: SyntaxKind) -> AssertionParts {
    let (node, record) = parsed
        .arena
        .iter()
        .find(|(_, record)| record.kind == kind)
        .expect("the source has the requested assertion");
    let (operand, target) = match &record.data {
        NodeData::AsExpression(assertion) => (assertion.expression, assertion.type_),
        NodeData::SatisfiesExpression(assertion) => (assertion.expression, assertion.type_),
        _ => panic!("expected an as or satisfies expression"),
    };
    assert_eq!(parsed.arena.get(operand).unwrap().parent, Some(node));
    assert_eq!(parsed.arena.get(target).unwrap().parent, Some(node));
    AssertionParts {
        expression: NodeRef::new(parsed.arena.id(), FILE, node),
        operand: NodeRef::new(parsed.arena.id(), FILE, operand),
        target: NodeRef::new(parsed.arena.id(), FILE, target),
    }
}

fn default_owner(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    assertion: AssertionParts,
) -> SemanticSymbolId {
    let export = parsed
        .arena
        .get(assertion.expression.node)
        .unwrap()
        .parent
        .unwrap();
    let NodeData::ExportAssignment(assignment) = &parsed.arena.get(export).unwrap().data else {
        panic!("the assertion must be the direct default export expression");
    };
    assert!(!assignment.is_export_equals);
    assert_eq!(assignment.expression, assertion.expression.node);
    let export = NodeRef::new(parsed.arena.id(), FILE, export);
    let bound = context.file(FILE).unwrap().1;
    let owner = bound.symbol(export).unwrap();
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = context.store().symbol(module).unwrap().exports().unwrap();
    assert_eq!(
        context
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source("default"),
        Some(owner),
    );
    let symbol = context.store().symbol(owner).unwrap();
    assert_eq!(symbol.flags(), SymbolFlags::PROPERTY);
    assert_eq!(symbol.value_declaration(), Some(export));
    assert_eq!(symbol.declarations(), Some(&[export][..]));
    owner
}

fn named_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
) -> SemanticSymbolId {
    let node = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::ImportSpecifier(import) => import.name,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::FunctionDeclaration(function) => function.name?,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source declares {expected}"));
    context.file(file).unwrap().1.symbol(node).unwrap()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .expect("source checking publishes the node type")
}

fn assert_default_assertion(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    assertion: AssertionParts,
    owner: SemanticSymbolId,
) -> (TypeId, TypeId) {
    assert_eq!(default_owner(context, parsed, assertion), owner);
    let target = resolved_type(context, assertion.target);
    let operand = resolved_type(context, assertion.operand);
    assert_eq!(resolved_type(context, assertion.expression), target);
    assert_eq!(
        context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(target),
    );
    assert_eq!(
        context.store().assertion_links(assertion.expression),
        Some(&AssertionLinks {
            expr_type: Some(operand)
        }),
    );
    let source = context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .unwrap();
    assert!(source.type_checked);
    assert_eq!(
        source.deferred_nodes.iter().copied().collect::<Vec<_>>(),
        [assertion.expression],
    );
    (target, operand)
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    nodes: &[NodeRef],
    symbols: &[SemanticSymbolId],
) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .clone(),
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        assertions: nodes
            .iter()
            .map(|&node| store.assertion_links(node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|&node| store.signature_links(node).cloned())
            .collect(),
        values: symbols
            .iter()
            .map(|&symbol| store.value_symbol_links(symbol).cloned())
            .collect(),
        aliases: symbols
            .iter()
            .map(|&symbol| store.alias_symbol_links(symbol).cloned())
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay_stable(
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &[NodeRef],
    symbols: &[SemanticSymbolId],
) {
    let checked = snapshot(context, nodes, symbols);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, nodes, symbols), checked);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, nodes, symbols), checked);
}

#[test]
fn local_annotated_call_default_assertion_keeps_the_binder_owner() {
    let source = parse_source_file(concat!(
        "function defineConfig(value: number): number { return value; } ",
        "export default defineConfig(1) as number;",
    ));
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::External, None);
    let owner = default_owner(&context, &source, assertion);
    let function = named_symbol(&context, &source, FILE, "defineConfig");
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(
        context
            .store()
            .assertion_links(assertion.expression)
            .is_none()
    );

    context.check_source_file(FILE).unwrap();

    let (target, operand) = assert_default_assertion(&context, &source, assertion, owner);
    assert_eq!(
        target,
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert_eq!(operand, target);
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(&mut context, &assertion.nodes(), &[owner, function]);
    assert_default_assertion(&context, &source, assertion, owner);
}

#[test]
fn local_structural_default_assertion_keeps_target_and_operand_separate() {
    let source = parse_source_file("export default { value: 1 } as { value: number };");
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::External, None);
    let owner = default_owner(&context, &source, assertion);
    assert!(context.store().value_symbol_links(owner).is_none());

    context.check_source_file(FILE).unwrap();

    let (target, operand) = assert_default_assertion(&context, &source, assertion, owner);
    assert_ne!(target, operand);
    assert_eq!(
        context.type_to_string(target).unwrap(),
        "{ value: number; }"
    );
    assert!(context.diagnostics().is_empty());
    let checked = snapshot(&context, &assertion.nodes(), &[owner]);
    assert_eq!(
        context.get_type_at_location(assertion.expression).unwrap(),
        target
    );
    assert_eq!(
        context.get_type_at_location(assertion.operand).unwrap(),
        operand
    );
    assert_eq!(snapshot(&context, &assertion.nodes(), &[owner]), checked);
    assert_replay_stable(&mut context, &assertion.nodes(), &[owner]);
    assert_default_assertion(&context, &source, assertion, owner);
}

// Importer and provider identities and both replay orders form one control.
#[test]
#[allow(clippy::too_many_lines)]
fn imported_call_default_assertion_keeps_the_type_only_target_out_of_values() {
    let source = parse_source_file(
        "import { type ViteUserConfig, defineConfig } from './provider'; export default defineConfig({ value: 1 }) as ViteUserConfig;",
    );
    let provider = parse_source_file(CONFIG_PROVIDER);
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::External, Some(&provider));
    let owner = default_owner(&context, &source, assertion);
    let imported_type = named_symbol(&context, &source, FILE, "ViteUserConfig");
    let imported_function = named_symbol(&context, &source, FILE, "defineConfig");
    let declared_type = named_symbol(&context, &provider, PROVIDER, "ViteUserConfig");
    let declared_function = named_symbol(&context, &provider, PROVIDER, "defineConfig");
    let symbols = [
        owner,
        imported_type,
        imported_function,
        declared_type,
        declared_function,
    ];
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().alias_symbol_links(imported_type).is_none());
    assert!(
        context
            .store()
            .alias_symbol_links(imported_function)
            .is_none()
    );

    context.check_source_file(FILE).unwrap();

    let (target, operand) = assert_default_assertion(&context, &source, assertion, owner);
    assert_ne!(target, operand);
    assert_eq!(context.type_to_string(target).unwrap(), "ViteUserConfig");
    assert_eq!(
        context.type_to_string(operand).unwrap(),
        "{ value: number; }"
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(declared_type)
            .unwrap()
            .declared_type,
        Some(target),
    );
    for (alias, target) in [
        (imported_type, declared_type),
        (imported_function, declared_function),
    ] {
        assert_eq!(
            context
                .store()
                .alias_symbol_links(alias)
                .unwrap()
                .alias_target,
            AliasTargetState::Resolved(target),
        );
    }
    for symbol in [imported_type, declared_type] {
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
    let callable = context
        .store()
        .value_symbol_links(declared_function)
        .unwrap()
        .resolved_type;
    assert!(callable.is_some());
    assert_eq!(
        context
            .store()
            .value_symbol_links(imported_function)
            .unwrap()
            .resolved_type,
        callable
    );
    let provider_source = context.source_file(PROVIDER).unwrap();
    assert!(
        !context
            .store()
            .source_file_links(provider_source)
            .is_some_and(|links| links.type_checked),
        "importer-first annotation lookup must not check the provider body",
    );
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(&mut context, &assertion.nodes(), &symbols);

    context.check_source_file(PROVIDER).unwrap();
    assert!(
        context
            .store()
            .source_file_links(provider_source)
            .unwrap()
            .type_checked
    );
    assert_default_assertion(&context, &source, assertion, owner);
    for symbol in [imported_type, declared_type] {
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
    let checked = snapshot(&context, &assertion.nodes(), &symbols);
    context.recheck_source_file(PROVIDER).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(snapshot(&context, &assertion.nodes(), &symbols), checked);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn imported_literal_default_assertion_uses_the_interface_as_context_only() {
    let source = parse_source_file(concat!(
        "import { type ViteUserConfig } from './provider'; ",
        "export default { value: 1 } as ViteUserConfig;",
    ));
    let provider = parse_source_file(CONFIG_PROVIDER);
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::External, Some(&provider));
    let owner = default_owner(&context, &source, assertion);
    let imported_type = named_symbol(&context, &source, FILE, "ViteUserConfig");
    let declared_type = named_symbol(&context, &provider, PROVIDER, "ViteUserConfig");
    assert!(context.store().value_symbol_links(owner).is_none());

    context.check_source_file(FILE).unwrap();

    let (target, operand) = assert_default_assertion(&context, &source, assertion, owner);
    assert_ne!(target, operand);
    assert_eq!(context.type_to_string(target).unwrap(), "ViteUserConfig");
    assert_eq!(
        context
            .store()
            .declared_type_links(declared_type)
            .unwrap()
            .declared_type,
        Some(target),
    );
    assert_eq!(
        context
            .store()
            .alias_symbol_links(imported_type)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(declared_type),
    );
    for symbol in [imported_type, declared_type] {
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(
        &mut context,
        &assertion.nodes(),
        &[owner, imported_type, declared_type],
    );
    assert_default_assertion(&context, &source, assertion, owner);
}

#[test]
fn imported_satisfies_target_does_not_replace_the_object_result() {
    let source = parse_source_file(concat!(
        "import { type ViteUserConfig } from './provider'; ",
        "const checked = { value: 1 } satisfies ViteUserConfig;",
    ));
    let provider = parse_source_file(CONFIG_PROVIDER);
    let assertion = assertion_parts(&source, SyntaxKind::SatisfiesExpression);
    let mut context = context(&source, CanonicalModuleState::External, Some(&provider));
    let variable = named_symbol(&context, &source, FILE, "checked");
    let imported_type = named_symbol(&context, &source, FILE, "ViteUserConfig");
    let declared_type = named_symbol(&context, &provider, PROVIDER, "ViteUserConfig");

    context.check_source_file(FILE).unwrap();

    let result = resolved_type(&context, assertion.expression);
    let target = resolved_type(&context, assertion.target);
    assert_eq!(result, resolved_type(&context, assertion.operand));
    assert_ne!(result, target);
    assert_eq!(
        context.type_to_string(result).unwrap(),
        "{ value: number; }"
    );
    assert_eq!(context.type_to_string(target).unwrap(), "ViteUserConfig");
    assert_eq!(
        context
            .store()
            .declared_type_links(declared_type)
            .unwrap()
            .declared_type,
        Some(target),
    );
    assert_eq!(
        context
            .store()
            .alias_symbol_links(imported_type)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(declared_type),
    );
    for symbol in [imported_type, declared_type] {
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
    assert!(
        context
            .store()
            .assertion_links(assertion.expression)
            .is_none()
    );
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .deferred_nodes
            .is_empty(),
    );
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(
        &mut context,
        &assertion.nodes(),
        &[variable, imported_type, declared_type],
    );
}

#[test]
fn nonoverlapping_default_assertion_reports_ts2352_once() {
    let source = parse_source_file("export default 1 as string;");
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::External, None);
    let owner = default_owner(&context, &source, assertion);

    context.check_source_file(FILE).unwrap();

    let (target, operand) = assert_default_assertion(&context, &source, assertion, owner);
    assert_eq!(
        target,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_ne!(target, operand);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the nonoverlapping cast must issue one diagnostic");
    };
    assert_eq!(diagnostic.node, Some(assertion.expression));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2352);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Conversion of type 'number' to type 'string' may be a mistake because neither type sufficiently overlaps with the other. If this was intentional, convert the expression to 'unknown' first.",
    );
    assert!(diagnostic.related_information.is_empty());
    assert_replay_stable(&mut context, &assertion.nodes(), &[owner]);
    assert_default_assertion(&context, &source, assertion, owner);
}

#[test]
fn default_satisfies_remains_unsupported_without_publishing_source_values() {
    let source = parse_source_file("export default 1 satisfies number;");
    let assertion = assertion_parts(&source, SyntaxKind::SatisfiesExpression);
    let mut context = context(&source, CanonicalModuleState::External, None);
    let owner = default_owner(&context, &source, assertion);
    let source_ref = context.source_file(FILE).unwrap();
    let before_source = context.store().source_file_links(source_ref).cloned();
    let before_counts = [
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
    ];
    assert!(
        before_source
            .as_ref()
            .is_none_or(|links| !links.type_checked && links.deferred_nodes.is_empty()),
    );
    assert!(context.store().value_symbol_links(owner).is_none());

    let result = context.check_source_file(FILE);

    assert!(
        matches!(
            result,
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node,
                kind: SyntaxKind::SatisfiesExpression,
                role: SourceSyntaxRole::Statement,
            })) if node == assertion.expression
        ),
        "expected the default satisfies expression boundary: {result:?}",
    );
    assert_eq!(
        context.store().source_file_links(source_ref),
        before_source.as_ref()
    );
    assert_eq!(
        [
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        ],
        before_counts,
    );
    assert!(context.store().value_symbol_links(owner).is_none());
    for node in assertion.nodes() {
        assert!(context.store().type_node_links(node).is_none());
    }
    assert!(
        context
            .store()
            .assertion_links(assertion.expression)
            .is_none()
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn local_satisfies_keeps_the_operand_type_without_a_deferred_cast() {
    let source = parse_source_file("const value = 1 satisfies number;");
    let assertion = assertion_parts(&source, SyntaxKind::SatisfiesExpression);
    let mut context = context(&source, CanonicalModuleState::Script, None);
    let variable = named_symbol(&context, &source, FILE, "value");

    context.check_source_file(FILE).unwrap();

    let result = resolved_type(&context, assertion.expression);
    let target = resolved_type(&context, assertion.target);
    assert_eq!(result, resolved_type(&context, assertion.operand));
    assert_ne!(result, target);
    assert_eq!(context.type_to_string(result).unwrap(), "1");
    assert_eq!(
        target,
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert!(
        context
            .store()
            .assertion_links(assertion.expression)
            .is_none()
    );
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .deferred_nodes
            .is_empty(),
    );
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(&mut context, &assertion.nodes(), &[variable]);
}

#[test]
fn local_const_assertion_keeps_the_literal_without_resolving_const_as_a_type() {
    let source = parse_source_file("const value = 1 as const;");
    let assertion = assertion_parts(&source, SyntaxKind::AsExpression);
    let mut context = context(&source, CanonicalModuleState::Script, None);
    let variable = named_symbol(&context, &source, FILE, "value");

    context.check_source_file(FILE).unwrap();

    let result = resolved_type(&context, assertion.expression);
    let operand = resolved_type(&context, assertion.operand);
    let TypeData::Literal(literal) = context.store().type_payload(result).unwrap().data() else {
        panic!("as const must retain the numeric literal");
    };
    assert_eq!(literal.regular_type, result);
    assert_eq!(context.type_to_string(result).unwrap(), "1");
    assert_eq!(
        context
            .store()
            .value_symbol_links(variable)
            .unwrap()
            .resolved_type,
        Some(result)
    );
    assert_eq!(
        context.store().assertion_links(assertion.expression),
        Some(&AssertionLinks {
            expr_type: Some(operand)
        }),
    );
    assert!(
        context
            .store()
            .type_node_links(assertion.target)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .deferred_nodes
            .is_empty(),
    );
    assert!(context.diagnostics().is_empty());
    assert_replay_stable(&mut context, &assertion.nodes(), &[variable]);
}
