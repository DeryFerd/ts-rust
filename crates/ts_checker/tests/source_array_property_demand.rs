use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_401);
const AUGMENTATION_FILE: FileId = FileId::new(203_402);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

struct Fixture {
    text: &'static str,
    source: ParseResult,
    libraries: Vec<ParseResult>,
    augmentation: Option<ParseResult>,
}

impl Fixture {
    fn new(text: &'static str, augmentation: Option<&str>) -> Self {
        let parse = |text| {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            parsed
        };
        Self {
            text,
            source: parse(text),
            libraries: LIBRARIES.iter().map(|(_, text)| parse(text)).collect(),
            augmentation: augmentation.map(parse),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/lib/{}\"", LIBRARIES[index].0),
                    true,
                    true,
                )
            })
            .collect::<Vec<_>>();
        if let Some(parsed) = &self.augmentation {
            files.push((
                AUGMENTATION_FILE,
                parsed,
                "\"/project/array-augmentation.d.ts\"".to_owned(),
                true,
                false,
            ));
        }
        files.push((
            FILE,
            &self.source,
            "\"/project/array-property.ts\"".to_owned(),
            false,
            false,
        ));
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, declaration, default_library) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *declaration,
                        *default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                strict_function_types: true,
                no_implicit_any: true,
                no_unchecked_indexed_access: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn access(&self, text: &str) -> NodeRef {
        let accesses = self
            .source
            .arena
            .iter()
            .filter_map(|(id, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression
                    && &self.text
                        [record.range.start.get() as usize..record.range.end.get() as usize]
                        == text)
                    .then_some(node(&self.source, FILE, id))
            })
            .collect::<Vec<_>>();
        let [access] = accesses.as_slice() else {
            panic!("one property access for {text}")
        };
        *access
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn property(parsed: &ParseResult, file: FileId, owner: &str, name: &str) -> NodeRef {
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name).unwrap().data
            else {
                return None;
            };
            (identifier.text == owner).then_some(interface)
        })
        .flat_map(|interface| interface.members.nodes.iter().copied())
        .filter_map(|id| {
            let NodeData::PropertyDeclaration(property) =
                &parsed.arena.get(id).unwrap().data
            else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(property.name).unwrap().data
            else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = declarations.as_slice() else {
        panic!("one source property {owner}.{name}")
    };
    *declaration
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

#[derive(Clone, Copy)]
enum Primitive {
    String,
    Number,
}

impl Primitive {
    fn type_id(self, checker: &CanonicalCheckerContext<'_>) -> TypeId {
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        match self {
            Self::String => bootstrap.string_type,
            Self::Number => bootstrap.number_type,
        }
    }
}

struct Read {
    access: NodeRef,
    declaration: NodeRef,
    element: Primitive,
    value: Primitive,
    readonly: bool,
    generic_property: bool,
}

#[derive(Debug, PartialEq, Eq)]
struct ReadState {
    receiver: TypeId,
    value: TypeId,
    source_symbol: SemanticSymbolId,
    source_template: TypeId,
}

fn observe(
    fixture: &Fixture,
    checker: &mut CanonicalCheckerContext<'_>,
    reads: &[Read],
) -> Vec<ReadState> {
    reads
        .iter()
        .map(|read| {
            let NodeData::PropertyAccessExpression(access) =
                &fixture.source.arena.get(read.access.node).unwrap().data
            else {
                unreachable!()
            };
            let expected = read.value.type_id(checker);
            let value = checker.get_type_at_location(read.access).unwrap();
            assert_eq!(value, expected);
            let source_symbol = symbol(checker, read.declaration);
            assert_eq!(
                checker.get_symbol_at_location(read.access),
                Ok(Some(source_symbol))
            );
            assert_eq!(
                checker.get_symbol_at_location(node(&fixture.source, FILE, access.name)),
                Ok(Some(source_symbol))
            );
            assert!(
                checker
                    .get_symbol_declarations(source_symbol)
                    .unwrap()
                    .contains(&read.declaration)
            );

            let receiver = checker
                .get_type_at_location(node(&fixture.source, FILE, access.expression))
                .unwrap();
            let TypeData::TypeReference(reference) =
                checker.store().type_payload(receiver).unwrap().data()
            else {
                panic!("the receiver must retain its real array reference")
            };
            let target = if read.readonly {
                checker.global_types().readonly_array_type
            } else {
                checker.global_types().array_type
            };
            assert_eq!(reference.object.target, Some(target));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[read.element.type_id(checker)][..])
            );

            let record = checker.store().symbol(source_symbol).unwrap();
            assert_eq!(record.flags(), SymbolFlags::PROPERTY);
            assert_eq!(
                record.check_flags().contains(CheckFlags::READONLY),
                read.readonly
            );
            let source_template = checker
                .store()
                .value_symbol_links(source_symbol)
                .and_then(|links| links.resolved_type)
                .expect("the selected declaration must have a queried type");
            if read.generic_property {
                assert!(matches!(
                    checker
                        .store()
                        .type_payload(source_template)
                        .unwrap()
                        .data(),
                    TypeData::TypeParameter(_)
                ));
                assert_ne!(
                    value, source_template,
                    "a receiver must not expose the source T"
                );
            } else {
                assert_eq!(source_template, value);
            }
            ReadState {
                receiver,
                value,
                source_symbol,
                source_template,
            }
        })
        .collect()
}

fn check_orders(fixture: &Fixture, reads: &[Read]) {
    for query_first in [false, true] {
        let mut checker = fixture.context();
        for read in reads {
            let source_symbol = symbol(&checker, read.declaration);
            assert!(
                checker
                    .store()
                    .value_symbol_links(source_symbol)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
        let first = query_first.then(|| checker.get_type_at_location(reads[0].access).unwrap());
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let state = observe(fixture, &mut checker, reads);
        if let Some(first) = first {
            assert_eq!(first, state[0].value);
        }
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(observe(fixture, &mut checker, reads), state);
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn real_array_length_demands_cold_types_and_keeps_source_symbols() {
    let fixture = Fixture::new(
        "declare const values: Array<string>;\ndeclare const frozen: ReadonlyArray<number>;\nconst count: number = values.length;\nconst frozenCount: number = frozen.length;\n",
        None,
    );
    let es5 = &fixture.libraries[0];
    check_orders(
        &fixture,
        &[
            Read {
                access: fixture.access("values.length"),
                declaration: property(es5, FileId::new(0), "Array", "length"),
                element: Primitive::String,
                value: Primitive::Number,
                readonly: false,
                generic_property: false,
            },
            Read {
                access: fixture.access("frozen.length"),
                declaration: property(es5, FileId::new(0), "ReadonlyArray", "length"),
                element: Primitive::Number,
                value: Primitive::Number,
                readonly: true,
                generic_property: false,
            },
        ],
    );
}

#[test]
fn real_array_data_property_maps_each_receiver_and_keeps_source_symbols() {
    let fixture = Fixture::new(
        "declare const strings: Array<string>;\ndeclare const numbers: Array<number>;\nconst text: string = strings.headValue;\nconst amount: number = numbers.headValue;\n",
        Some("interface Array<T> { headValue: T; }\n"),
    );
    let declaration = property(
        fixture.augmentation.as_ref().unwrap(),
        AUGMENTATION_FILE,
        "Array",
        "headValue",
    );
    check_orders(
        &fixture,
        &[
            Read {
                access: fixture.access("strings.headValue"),
                declaration,
                element: Primitive::String,
                value: Primitive::String,
                readonly: false,
                generic_property: true,
            },
            Read {
                access: fixture.access("numbers.headValue"),
                declaration,
                element: Primitive::Number,
                value: Primitive::Number,
                readonly: false,
                generic_property: true,
            },
        ],
    );
}
