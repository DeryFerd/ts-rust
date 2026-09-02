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
const ADDITIONAL_AUGMENTATION: usize = 4;
const CONSUMER: usize = 5;
const FILES: [FileId; 6] = [
    FileId::new(470_140),
    FileId::new(470_141),
    FileId::new(470_142),
    FileId::new(470_143),
    FileId::new(470_144),
    FileId::new(470_145),
];
const PATHS: [&str; 6] = [
    "/project/src/context.ts",
    "/project/src/index.ts",
    "/project/src/middleware/plugin/provider.ts",
    "/project/src/middleware/plugin/index.ts",
    "/project/src/middleware/plugin/additional.ts",
    "/project/consumer.ts",
];

#[derive(Clone, Copy)]
struct Provider {
    source: &'static str,
    name: &'static str,
    kind: SyntaxKind,
    property: &'static str,
    optional: bool,
}

const PROVIDERS: [Provider; 3] = [
    Provider {
        source: "export interface LanguageVariables { language: string }\n",
        name: "LanguageVariables",
        kind: SyntaxKind::InterfaceDeclaration,
        property: "language",
        optional: false,
    },
    Provider {
        source: "export type RequestIdVariables = { requestId: string };\n",
        name: "RequestIdVariables",
        kind: SyntaxKind::TypeAliasDeclaration,
        property: "requestId",
        optional: false,
    },
    Provider {
        source: "export type SecureHeadersVariables = { secureHeadersNonce?: string };\n",
        name: "SecureHeadersVariables",
        kind: SyntaxKind::TypeAliasDeclaration,
        property: "secureHeadersNonce",
        optional: true,
    },
];

struct Fixture {
    sources: [ParseResult; 6],
}

impl Fixture {
    fn new(provider: Provider, own_member: &str, read_type: &str) -> Self {
        Self {
            sources: [
                parse_source_file("export interface ContextVariableMap { existing: number }\n"),
                parse_source_file("export type { ContextVariableMap } from './context';\n"),
                parse_source_file(&format!(
                    "{}export interface AdditionalVariables {{ additional: boolean }}\n",
                    provider.source,
                )),
                parse_source_file(&format!(
                    "import type {{ {} as ImportedVariables }} from './provider';\n\
                     export type {{ ImportedVariables }};\n\
                     declare module '../..' {{\n\
                       interface ContextVariableMap extends ImportedVariables {{ {own_member} }}\n\
                     }}\n",
                    provider.name,
                )),
                parse_source_file(concat!(
                    "import type { AdditionalVariables as ImportedAdditional } from './provider';\n",
                    "export type { ImportedAdditional };\n",
                    "declare module '../..' {\n",
                    "  interface ContextVariableMap extends ImportedAdditional {}\n",
                    "}\n",
                )),
                parse_source_file(&format!(
                    "import type {{ ContextVariableMap as Variables }} from './src';\n\
                     declare const variables: Variables;\n\
                     const own: number = variables.existing;\n\
                     const added: boolean = variables.additional;\n\
                     const inherited: {read_type} = variables.{};\n",
                    provider.property,
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
            (AUGMENTATION, "./provider", PROVIDER),
            (AUGMENTATION, "../..", ROOT),
            (ADDITIONAL_AUGMENTATION, "./provider", PROVIDER),
            (ADDITIONAL_AUGMENTATION, "../..", ROOT),
            (CONSUMER, "./src", ROOT),
        ]
        .map(|(source, specifier, target)| {
            CanonicalModuleResolutionEntry::resolved(
                self.module_specifier(source, specifier),
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

    fn module_specifier(&self, index: usize, expected: &str) -> NodeRef {
        let parsed = &self.sources[index];
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::StringLiteral(value) = &record.data else {
                    return None;
                };
                (value.text == expected)
                    .then_some(NodeRef::new(parsed.arena.id(), FILES[index], node))
            })
            .unwrap_or_else(|| panic!("missing module specifier {expected}"))
    }

    fn declaration(&self, index: usize, kind: SyntaxKind, expected: &str) -> NodeRef {
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
                    _ => return None,
                };
                let text = match &parsed.arena.get(name)?.data {
                    NodeData::Identifier(name) => name.text.as_str(),
                    NodeData::StringLiteral(name) => name.text.as_str(),
                    _ => return None,
                };
                (text == expected)
                    .then_some(NodeRef::new(parsed.arena.id(), FILES[index], node))
            })
            .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
    }

    fn source_node(&self, index: usize) -> NodeRef {
        let parsed = &self.sources[index];
        NodeRef::new(parsed.arena.id(), FILES[index], parsed.source_file)
    }

    fn read(&self, property: &str) -> NodeRef {
        let parsed = &self.sources[CONSUMER];
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                    return None;
                };
                (name.text == property)
                    .then_some(NodeRef::new(parsed.arena.id(), FILES[CONSUMER], node))
            })
            .unwrap_or_else(|| panic!("missing property read {property}"))
    }

    fn text(&self, node: NodeRef) -> &str {
        let index = FILES.iter().position(|file| *file == node.file).unwrap();
        let parsed = &self.sources[index];
        assert_eq!(node.arena, parsed.arena.id());
        let range = parsed.arena.get(node.node).unwrap().range;
        &parsed.arena.source_text().unwrap()
            [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
    }
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .store()
        .get_merged_symbol(raw_symbol(checker, declaration))
        .unwrap()
}

fn merged_owner(fixture: &Fixture, checker: &CanonicalCheckerContext<'_>) -> SemanticSymbolId {
    let original =
        fixture.declaration(CONTEXT, SyntaxKind::InterfaceDeclaration, "ContextVariableMap");
    let owner = symbol(checker, original);
    let augmentations = [AUGMENTATION, ADDITIONAL_AUGMENTATION].map(|index| {
        let declaration =
            fixture.declaration(index, SyntaxKind::InterfaceDeclaration, "ContextVariableMap");
        assert_ne!(raw_symbol(checker, original), raw_symbol(checker, declaration));
        assert_eq!(symbol(checker, declaration), owner);
        declaration
    });
    assert_ne!(
        raw_symbol(checker, augmentations[0]),
        raw_symbol(checker, augmentations[1]),
    );
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(
        record.flags().without(SymbolFlags::TRANSIENT),
        SymbolFlags::INTERFACE,
    );
    assert_eq!(
        record.declarations(),
        Some([original, augmentations[0], augmentations[1]].as_slice()),
    );
    let root = symbol(checker, fixture.source_node(ROOT));
    assert_eq!(
        checker.store().get_parent_of_symbol(owner),
        Some(root),
    );
    for index in [AUGMENTATION, ADDITIONAL_AUGMENTATION] {
        let module = fixture.declaration(index, SyntaxKind::ModuleDeclaration, "../..");
        assert_eq!(symbol(checker, module), root);
    }
    let exported = checker
        .store()
        .symbol_table(checker.store().symbol(root).unwrap().exports().unwrap())
        .unwrap()
        .get_source("ContextVariableMap")
        .unwrap();
    assert_eq!(checker.store().get_merged_symbol(exported), Some(owner));
    owner
}

fn assert_import_target(
    fixture: &Fixture,
    checker: &CanonicalCheckerContext<'_>,
    index: usize,
    name: &str,
    expected: SemanticSymbolId,
) {
    let import = fixture.declaration(index, SyntaxKind::ImportSpecifier, name);
    let alias = symbol(checker, import);
    assert_ne!(alias, expected);
    assert_eq!(
        checker.store().symbol(alias).unwrap().flags(),
        SymbolFlags::ALIAS,
    );
    let AliasTargetState::Resolved(target) =
        checker.store().alias_symbol_links(alias).unwrap().alias_target
    else {
        panic!("the actual type import must retain its resolved target")
    };
    assert_eq!(checker.store().get_merged_symbol(target), Some(expected));
    assert!(checker.store().value_symbol_links(alias).is_none());
}

fn property(checker: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    let structured = match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::Object(data) => &data.structured,
        _ => panic!("the inherited property must belong to its canonical object type"),
    };
    checker
        .store()
        .symbol_table(structured.members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn check_files(checker: &mut CanonicalCheckerContext<'_>, order: [usize; 6]) {
    for index in order {
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

#[test]
#[allow(clippy::too_many_lines)] // Each source shape keeps the same import and augmentation graph.
fn imported_augmentation_bases_keep_merged_owner_and_property_types() {
    for provider in PROVIDERS {
        let read_type = if provider.optional {
            "string | undefined"
        } else {
            "string"
        };
        let fixture = Fixture::new(provider, "", read_type);
        for provider_first in [false, true] {
            let mut checker = fixture.checker();
            let owner = merged_owner(&fixture, &checker);
            let base_owner = symbol(
                &checker,
                fixture.declaration(PROVIDER, provider.kind, provider.name),
            );
            let additional_owner = symbol(
                &checker,
                fixture.declaration(
                    PROVIDER,
                    SyntaxKind::InterfaceDeclaration,
                    "AdditionalVariables",
                ),
            );
            assert_ne!(owner, base_owner);
            assert_ne!(base_owner, additional_owner);
            if provider_first {
                checker.check_source_file(FILES[PROVIDER]).unwrap();
            }
            check_files(
                &mut checker,
                [
                    AUGMENTATION,
                    ADDITIONAL_AUGMENTATION,
                    CONTEXT,
                    ROOT,
                    PROVIDER,
                    CONSUMER,
                ],
            );
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
            assert_import_target(
                &fixture,
                &checker,
                AUGMENTATION,
                "ImportedVariables",
                base_owner,
            );
            assert_import_target(
                &fixture,
                &checker,
                ADDITIONAL_AUGMENTATION,
                "ImportedAdditional",
                additional_owner,
            );
            assert_import_target(&fixture, &checker, CONSUMER, "Variables", owner);
            let owner_type = checker.get_declared_type_of_symbol(owner).unwrap();
            let base_type = checker.get_declared_type_of_symbol(base_owner).unwrap();
            let additional_type = checker
                .get_declared_type_of_symbol(additional_owner)
                .unwrap();
            let TypeData::Interface(data) =
                checker.store().type_payload(owner_type).unwrap().data()
            else {
                panic!("the merged owner must retain its interface type")
            };
            assert!(data.base_types_resolved);
            assert_eq!(
                data.resolved_base_types.as_deref(),
                Some([base_type, additional_type].as_slice()),
            );
            let inherited = property(&checker, owner_type, provider.property);
            assert_eq!(inherited, property(&checker, base_type, provider.property));
            assert_eq!(
                property(&checker, owner_type, "additional"),
                property(&checker, additional_type, "additional"),
            );
            assert_eq!(
                checker
                    .store()
                    .symbol(inherited)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::OPTIONAL),
                provider.optional,
            );
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let (number, string, undefined, boolean) = (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.boolean_type,
            );
            assert_eq!(
                checker.get_type_at_location(fixture.read("existing")),
                Ok(number),
            );
            assert_eq!(
                checker.get_type_at_location(fixture.read("additional")),
                Ok(boolean),
            );
            let read = fixture.read(provider.property);
            let value = checker.get_type_at_location(read).unwrap();
            if provider.optional {
                let TypeData::Union(union) = checker.store().type_payload(value).unwrap().data()
                else {
                    panic!("the optional property read must retain undefined")
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&string));
                assert!(union.union.types.contains(&undefined));
            } else {
                assert_eq!(value, string);
            }
            let warm = snapshot(&checker);
            for _ in 0..2 {
                for file in FILES {
                    checker.recheck_source_file(file).unwrap();
                }
                assert_eq!(merged_owner(&fixture, &checker), owner);
                assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(owner_type));
                assert_eq!(checker.get_declared_type_of_symbol(base_owner), Ok(base_type));
                assert_eq!(checker.get_type_at_location(read), Ok(value));
                assert_import_target(
                    &fixture,
                    &checker,
                    AUGMENTATION,
                    "ImportedVariables",
                    base_owner,
                );
                assert_import_target(
                    &fixture,
                    &checker,
                    ADDITIONAL_AUGMENTATION,
                    "ImportedAdditional",
                    additional_owner,
                );
                assert_import_target(&fixture, &checker, CONSUMER, "Variables", owner);
                assert_eq!(
                    snapshot(&checker),
                    warm,
                    "{}, provider_first={provider_first}",
                    provider.name,
                );
            }
        }
    }
}

#[test]
fn imported_augmentation_interface_keeps_native_property_conflict() {
    let fixture = Fixture::new(PROVIDERS[0], "language: number", "number");
    let mut checker = fixture.checker();
    let owner = merged_owner(&fixture, &checker);
    check_files(
        &mut checker,
        [
            CONTEXT,
            ROOT,
            PROVIDER,
            AUGMENTATION,
            ADDITIONAL_AUGMENTATION,
            CONSUMER,
        ],
    );
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one incompatible inherited-property diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2430);
    let anchor = diagnostic.node.unwrap();
    assert_eq!(anchor.file, FILES[CONTEXT]);
    assert_eq!(fixture.text(anchor), "ContextVariableMap");
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Interface 'ContextVariableMap' incorrectly extends interface 'LanguageVariables'.\n",
            "  Types of property 'language' are incompatible.\n",
            "    Type 'number' is not assignable to type 'string'.",
        ),
    );
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        checker.get_type_at_location(fixture.read("language")),
        Ok(number),
    );
    let warm = snapshot(&checker);
    for _ in 0..2 {
        for file in FILES {
            checker.recheck_source_file(file).unwrap();
        }
        assert_eq!(merged_owner(&fixture, &checker), owner);
        assert_eq!(snapshot(&checker), warm);
    }
}
