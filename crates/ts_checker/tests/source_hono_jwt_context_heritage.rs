use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const CONTEXT: usize = 0;
const ROOT: usize = 1;
const PROVIDER: usize = 2;
const AUGMENTATION: usize = 3;
const CONSUMER: usize = 4;
const FILES: [FileId; 5] = [
    FileId::new(474_910),
    FileId::new(474_911),
    FileId::new(474_912),
    FileId::new(474_913),
    FileId::new(474_914),
];
const PATHS: [&str; 5] = [
    "/project/src/context.ts",
    "/project/src/index.ts",
    "/project/src/middleware/jwt/jwt.ts",
    "/project/src/middleware/jwt/index.ts",
    "/project/consumer.ts",
];

struct Fixture {
    sources: [ParseResult; 5],
}

impl Fixture {
    fn new(conflict: bool) -> Self {
        let member = if conflict { "jwtPayload: string" } else { "" };
        let numeric_read = if conflict { "string" } else { "number" };
        Self {
            sources: [
                parse_source_file(concat!(
                    "export interface ContextVariableMap { existing: number }\n",
                    "export interface NumericContextVariableMap {}\n",
                )),
                parse_source_file(
                    "export type { ContextVariableMap, NumericContextVariableMap } from './context';\n",
                ),
                parse_source_file("export type JwtVariables<T = any> = { jwtPayload: T };\n"),
                parse_source_file(&format!(
                    "import type {{ JwtVariables }} from './jwt';\n\
                     declare module '../..' {{\n\
                       interface ContextVariableMap extends JwtVariables<unknown> {{}}\n\
                       interface NumericContextVariableMap extends JwtVariables<number> {{ {member} }}\n\
                     }}\n",
                )),
                parse_source_file(&format!(
                    "import type {{ ContextVariableMap, NumericContextVariableMap }} from './src';\n\
                     declare const variables: ContextVariableMap;\n\
                     declare const numeric: NumericContextVariableMap;\n\
                     const existing: number = variables.existing;\n\
                     const payload: unknown = variables.jwtPayload;\n\
                     const numericPayload: {numeric_read} = numeric.jwtPayload;\n",
                )),
            ],
        }
    }

    fn checker(&self) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        for (index, parsed) in self.sources.iter().enumerate() {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FILES[index],
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"{}\"", PATHS[index])),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (index, parsed) in self.sources.iter().enumerate() {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FILES[index])
                .unwrap();
        }
        let resolutions = [
            (ROOT, "./context", CONTEXT),
            (AUGMENTATION, "./jwt", PROVIDER),
            (AUGMENTATION, "../..", ROOT),
            (CONSUMER, "./src", ROOT),
        ]
        .map(|(source, specifier, target)| {
            CanonicalModuleResolutionEntry::resolved(
                self.named_node(source, SyntaxKind::StringLiteral, specifier),
                CanonicalResolvedModuleInput::new(
                    FILES[target],
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        });
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            self.sources
                .iter()
                .enumerate()
                .map(|(index, source)| (FILES[index], &source.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
            CanonicalModuleResolutionManifestInput::new(resolutions),
        )
        .unwrap()
    }

    fn source_node(&self, index: usize) -> NodeRef {
        let parsed = &self.sources[index];
        NodeRef::new(parsed.arena.id(), FILES[index], parsed.source_file)
    }

    fn named_node(&self, index: usize, kind: SyntaxKind, expected: &str) -> NodeRef {
        let parsed = &self.sources[index];
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                if record.kind != kind {
                    return None;
                }
                let name = match &record.data {
                    NodeData::InterfaceDeclaration(data) => data.name,
                    NodeData::TypeAliasDeclaration(data) => data.name,
                    NodeData::ImportSpecifier(data) => data.name,
                    NodeData::ModuleDeclaration(data) => data.name,
                    NodeData::StringLiteral(_) => node,
                    _ => return None,
                };
                let text = match &parsed.arena.get(name)?.data {
                    NodeData::Identifier(name) => name.text.as_str(),
                    NodeData::StringLiteral(name) => name.text.as_str(),
                    _ => return None,
                };
                (text == expected).then_some(NodeRef::new(parsed.arena.id(), FILES[index], node))
            })
            .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
    }

    fn node_text(&self, node: NodeRef) -> &str {
        let index = FILES.iter().position(|file| *file == node.file).unwrap();
        let parsed = &self.sources[index];
        assert_eq!(parsed.arena.id(), node.arena);
        let range = parsed.arena.get(node.node).unwrap().range;
        &parsed.arena.source_text().unwrap()
            [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
    }

    fn expression(&self, index: usize, kind: SyntaxKind, text: &str) -> NodeRef {
        let parsed = &self.sources[index];
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let node = NodeRef::new(parsed.arena.id(), FILES[index], node);
                (record.kind == kind && self.node_text(node) == text).then_some(node)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} {text}"))
    }
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker
        .store()
        .get_merged_symbol(raw_symbol(checker, node))
        .unwrap()
}

fn merged_owner(
    fixture: &Fixture,
    checker: &CanonicalCheckerContext<'_>,
    name: &str,
) -> SemanticSymbolId {
    let original = fixture.named_node(CONTEXT, SyntaxKind::InterfaceDeclaration, name);
    let augmentation = fixture.named_node(AUGMENTATION, SyntaxKind::InterfaceDeclaration, name);
    let owner = symbol(checker, original);
    assert_ne!(
        raw_symbol(checker, original),
        raw_symbol(checker, augmentation)
    );
    assert_eq!(symbol(checker, augmentation), owner);
    let store = checker.store();
    let record = store.symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        record.declarations(),
        Some([original, augmentation].as_slice())
    );
    let root = symbol(checker, fixture.source_node(ROOT));
    assert_eq!(store.get_parent_of_symbol(owner), Some(root));
    assert_eq!(
        symbol(
            checker,
            fixture.named_node(AUGMENTATION, SyntaxKind::ModuleDeclaration, "../..")
        ),
        root,
    );
    let exported = store
        .symbol_table(store.symbol(root).unwrap().exports().unwrap())
        .unwrap()
        .get_source(name)
        .unwrap();
    assert_eq!(store.get_merged_symbol(exported), Some(owner));
    owner
}

fn assert_import_target(
    fixture: &Fixture,
    checker: &CanonicalCheckerContext<'_>,
    index: usize,
    name: &str,
    expected: SemanticSymbolId,
) {
    let alias = symbol(
        checker,
        fixture.named_node(index, SyntaxKind::ImportSpecifier, name),
    );
    assert_ne!(alias, expected);
    assert_eq!(
        checker.store().symbol(alias).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    assert_eq!(
        checker
            .store()
            .alias_symbol_links(alias)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(expected),
    );
    assert!(checker.store().value_symbol_links(alias).is_none());
}

fn property(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SemanticSymbolId {
    let structured = match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::Object(data) => &data.structured,
        _ => panic!("the payload must belong to an interface or alias object"),
    };
    checker
        .store()
        .symbol_table(structured.members.unwrap())
        .unwrap()
        .get_source("jwtPayload")
        .unwrap()
}

fn check_files(checker: &mut CanonicalCheckerContext<'_>) {
    for index in [CONTEXT, ROOT, PROVIDER, AUGMENTATION, CONSUMER] {
        checker
            .check_source_file(FILES[index])
            .unwrap_or_else(|error| panic!("{}: {error:?}", PATHS[index]));
    }
}

fn snapshot(checker: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.merged_symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
    )
}

#[allow(clippy::too_many_lines)] // Check the two source arguments against one alias template.
fn assert_types(
    fixture: &Fixture,
    checker: &mut CanonicalCheckerContext<'_>,
    conflict: bool,
) -> ([SemanticSymbolId; 3], [TypeId; 5], [SemanticSymbolId; 4]) {
    let owner = merged_owner(fixture, checker, "ContextVariableMap");
    let numeric_owner = merged_owner(fixture, checker, "NumericContextVariableMap");
    let alias_node = fixture.named_node(PROVIDER, SyntaxKind::TypeAliasDeclaration, "JwtVariables");
    let alias_owner = symbol(checker, alias_node);
    assert_ne!(owner, numeric_owner);
    assert_ne!(owner, alias_owner);
    assert_ne!(numeric_owner, alias_owner);
    assert_import_target(fixture, checker, AUGMENTATION, "JwtVariables", alias_owner);
    assert_import_target(fixture, checker, CONSUMER, "ContextVariableMap", owner);
    assert_import_target(
        fixture,
        checker,
        CONSUMER,
        "NumericContextVariableMap",
        numeric_owner,
    );

    let owner_type = checker.get_declared_type_of_symbol(owner).unwrap();
    let numeric_type = checker.get_declared_type_of_symbol(numeric_owner).unwrap();
    let template = checker.get_declared_type_of_symbol(alias_owner).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (unknown, number, string, any) = (
        bootstrap.unknown_type,
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.any_type,
    );
    assert_ne!(unknown, any);
    let mut bases = Vec::new();
    for (type_, argument, text) in [
        (owner_type, unknown, "JwtVariables<unknown>"),
        (numeric_type, number, "JwtVariables<number>"),
    ] {
        let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
            panic!("the merged declaration must keep its interface type")
        };
        assert!(data.this_type.is_some());
        assert!(data.base_types_resolved);
        let [base] = data.resolved_base_types.as_deref().unwrap() else {
            panic!("each interface must have its one written base")
        };
        let base = *base;
        let record = checker.store().type_payload(base).unwrap();
        let alias = checker.store().type_alias(record.alias().unwrap()).unwrap();
        assert_eq!(alias.symbol(), Some(alias_owner));
        assert_eq!(alias.type_arguments(), Some([argument].as_slice()));
        let reference =
            fixture.expression(AUGMENTATION, SyntaxKind::ExpressionWithTypeArguments, text);
        assert_eq!(
            checker
                .store()
                .symbol_node_links(reference)
                .unwrap()
                .resolved_symbol,
            Some(alias_owner),
        );
        assert_eq!(
            checker
                .store()
                .type_node_links(reference)
                .unwrap()
                .resolved_type,
            Some(base)
        );
        assert_ne!(base, template);
        bases.push(base);
    }
    assert_ne!(bases[0], bases[1]);

    let source_property = property(checker, template);
    let parameters = checker
        .store()
        .type_alias_links(alias_owner)
        .unwrap()
        .type_parameters
        .as_deref()
        .unwrap();
    let [parameter] = parameters else {
        panic!("JwtVariables must retain its one source parameter")
    };
    let NodeData::TypeAliasDeclaration(alias) = &fixture.sources[PROVIDER]
        .arena
        .get(alias_node.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let parameter_node = NodeRef::new(
        alias_node.arena,
        alias_node.file,
        alias.type_parameters.as_ref().unwrap().nodes[0],
    );
    assert_eq!(
        checker.store().type_payload(*parameter).unwrap().symbol(),
        Some(symbol(checker, parameter_node))
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(source_property)
            .unwrap()
            .resolved_type,
        Some(*parameter)
    );

    let inherited = [property(checker, bases[0]), property(checker, bases[1])];
    assert_ne!(inherited[0], inherited[1]);
    for (property, expected) in inherited.into_iter().zip([unknown, number]) {
        let links = checker.store().value_symbol_links(property).unwrap();
        assert_eq!(links.target, Some(source_property));
        assert!(links.mapper.is_some());
        assert_eq!(links.resolved_type, Some(expected));
        assert!(
            !checker
                .store()
                .symbol(property)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );
    }
    let own = [
        property(checker, owner_type),
        property(checker, numeric_type),
    ];
    assert_eq!(own[0], inherited[0]);
    let expected_numeric = if conflict { string } else { number };
    if conflict {
        assert_ne!(own[1], inherited[1]);
    } else {
        assert_eq!(own[1], inherited[1]);
    }
    assert_eq!(
        checker
            .store()
            .value_symbol_links(own[1])
            .unwrap()
            .resolved_type,
        Some(expected_numeric)
    );
    for (text, expected) in [
        ("variables.existing", number),
        ("variables.jwtPayload", unknown),
        ("numeric.jwtPayload", expected_numeric),
    ] {
        let read = fixture.expression(CONSUMER, SyntaxKind::PropertyAccessExpression, text);
        assert_eq!(checker.get_type_at_location(read), Ok(expected));
    }
    (
        [owner, numeric_owner, alias_owner],
        [owner_type, numeric_type, template, bases[0], bases[1]],
        [own[0], own[1], inherited[0], inherited[1]],
    )
}

fn assert_replay(fixture: &Fixture, checker: &mut CanonicalCheckerContext<'_>, conflict: bool) {
    let identities = assert_types(fixture, checker, conflict);
    let warm = snapshot(checker);
    for _ in 0..2 {
        for file in FILES {
            checker.recheck_source_file(file).unwrap();
        }
        assert_eq!(assert_types(fixture, checker, conflict), identities);
        assert_eq!(snapshot(checker), warm);
    }
}

#[test]
fn jwt_augmentation_keeps_explicit_unknown_and_number_instances() {
    let fixture = Fixture::new(false);
    for provider_first in [false, true] {
        let mut checker = fixture.checker();
        if provider_first {
            checker.check_source_file(FILES[PROVIDER]).unwrap();
        }
        check_files(&mut checker);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert_replay(&fixture, &mut checker, false);
    }
}

#[test]
fn jwt_augmentation_reports_native_property_conflict() {
    let fixture = Fixture::new(true);
    for provider_first in [false, true] {
        let mut checker = fixture.checker();
        if provider_first {
            checker.check_source_file(FILES[PROVIDER]).unwrap();
        }
        check_files(&mut checker);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected one TS2430: {:?}", checker.diagnostics())
        };
        assert_eq!(diagnostic.diagnostic.code(), 2430);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Interface 'NumericContextVariableMap' incorrectly extends interface 'JwtVariables<number>'.\n",
                "  Types of property 'jwtPayload' are incompatible.\n",
                "    Type 'string' is not assignable to type 'number'.",
            )
        );
        let node = diagnostic.node.unwrap();
        assert_eq!(node.file, FILES[CONTEXT]);
        assert_eq!(fixture.node_text(node), "NumericContextVariableMap");
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_replay(&fixture, &mut checker, true);
    }
}
