use ts_ast::{NodeData, SyntaxKind};
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

struct Case {
    name: &'static str,
    source: &'static str,
    fields: &'static [(&'static str, usize)],
    diagnostics: &'static [(u32, usize, &'static str)],
}

const DUPLICATE: &str = "Duplicate identifier 'value'.";
const NUMBER_TO_STRING: &str = "Type 'number' is not assignable to type 'string'.";
const STRING_TO_NUMBER: &str = "Type 'string' is not assignable to type 'number'.";
const DIFFERENT_TYPE: &str = "Subsequent property declarations must have the same type.  Property 'value' must be of type 'string', but here has type 'number'.";

// Expected types, symbol groups, and diagnostics come from the pinned Go checker.
const CASES: &[Case] = &[
    Case {
        name: "property then accessor",
        source: "class Model { value: number = 2; accessor value: number = 3; }",
        fields: &[("number", 0), ("number", 0)],
        diagnostics: &[(2300, 0, DUPLICATE), (2300, 1, DUPLICATE)],
    },
    Case {
        name: "accessor then property",
        source: "class Model { accessor value: number = 2; value: number = 3; }",
        fields: &[("number", 0), ("number", 0)],
        diagnostics: &[(2300, 0, DUPLICATE), (2300, 1, DUPLICATE)],
    },
    Case {
        name: "fields before between and after",
        source: "class Model { before: number = 1; value: number = 2; between: string = 'mid'; accessor value: number = 3; after: number = 4; }",
        fields: &[
            ("number", 0),
            ("number", 1),
            ("string", 2),
            ("number", 1),
            ("number", 3),
        ],
        diagnostics: &[(2300, 1, DUPLICATE), (2300, 3, DUPLICATE)],
    },
    Case {
        name: "static duplicates",
        source: "class Model { static before: number = 1; static value: number = 2; between: number = 9; static accessor value: number = 3; static after: string = 'end'; }",
        fields: &[
            ("number", 0),
            ("number", 1),
            ("number", 2),
            ("number", 1),
            ("string", 3),
        ],
        diagnostics: &[(2300, 1, DUPLICATE), (2300, 3, DUPLICATE)],
    },
    Case {
        name: "distinct static symbol",
        source: "class Model { static value: string = 'static'; value: number = 2; accessor value: number = 3; }",
        fields: &[("string", 0), ("number", 1), ("number", 1)],
        diagnostics: &[(2300, 1, DUPLICATE), (2300, 2, DUPLICATE)],
    },
    Case {
        name: "accessor annotation wins",
        source: "class Model { value: number = 2; accessor value: string = 'next'; }",
        fields: &[("string", 0), ("string", 0)],
        diagnostics: &[
            (2300, 0, DUPLICATE),
            (2322, 0, NUMBER_TO_STRING),
            (2300, 1, DUPLICATE),
        ],
    },
    Case {
        name: "secondary property annotation",
        source: "class Model { accessor value: string = 'next'; value: number = 2; }",
        fields: &[("string", 0), ("string", 0)],
        diagnostics: &[
            (2300, 0, DUPLICATE),
            (2300, 1, DUPLICATE),
            (2717, 1, DIFFERENT_TYPE),
        ],
    },
    Case {
        name: "three declarations",
        source: "class Model { value: number = 1; accessor value: number = 2; value: number = 3; }",
        fields: &[("number", 0), ("number", 0), ("number", 0)],
        diagnostics: &[
            (2300, 0, DUPLICATE),
            (2300, 1, DUPLICATE),
            (2300, 2, DUPLICATE),
        ],
    },
    Case {
        name: "two interleaved groups",
        source: "class Model { left: number = 1; right: string = 'a'; accessor left: number = 2; accessor right: string = 'b'; }",
        fields: &[("number", 0), ("string", 1), ("number", 0), ("string", 1)],
        diagnostics: &[
            (2300, 0, "Duplicate identifier 'left'."),
            (2300, 1, "Duplicate identifier 'right'."),
            (2300, 2, "Duplicate identifier 'left'."),
            (2300, 3, "Duplicate identifier 'right'."),
        ],
    },
    Case {
        name: "plain properties",
        source: "class Model { value: number = 1; value: number = 2; }",
        fields: &[("number", 0), ("number", 0)],
        diagnostics: &[(2300, 0, DUPLICATE), (2300, 1, DUPLICATE)],
    },
    Case {
        name: "inferred fields",
        source: "class Model { before = 0; value = 1; between = 'mid'; accessor value = 2; after = 'end'; }",
        fields: &[
            ("number", 0),
            ("number", 1),
            ("string", 2),
            ("number", 1),
            ("string", 3),
        ],
        diagnostics: &[(2300, 1, DUPLICATE), (2300, 3, DUPLICATE)],
    },
    Case {
        name: "inferred accessor wins",
        source: "class Model { value = 1; accessor value = 'next'; }",
        fields: &[("string", 0), ("string", 0)],
        diagnostics: &[
            (2300, 0, DUPLICATE),
            (2322, 0, NUMBER_TO_STRING),
            (2300, 1, DUPLICATE),
        ],
    },
    Case {
        name: "unrelated initializer error",
        source: "class Model { before: number = 'bad'; value: number = 1; accessor value: number = 2; }",
        fields: &[("number", 0), ("number", 1), ("number", 1)],
        diagnostics: &[
            (2322, 0, STRING_TO_NUMBER),
            (2300, 1, DUPLICATE),
            (2300, 2, DUPLICATE),
        ],
    },
];

#[test]
fn recovered_duplicate_properties_match_pinned_types_symbols_and_diagnostics() {
    for case in CASES {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/control.ts", case.source)
            .unwrap();
        let (program, fields) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["control.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::EsNext,
                strict: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let source = program.source_file("/project/control.ts").unwrap();
                let fields = source
                    .parse
                    .arena
                    .iter()
                    .filter_map(|(id, record)| {
                        let NodeData::PropertyDeclaration(property) = &record.data else {
                            return None;
                        };
                        Some((
                            source.node_ref(id).unwrap(),
                            source.node_ref(property.name).unwrap(),
                            property.type_.map(|node| source.node_ref(node).unwrap()),
                            source.node_ref(property.initializer.unwrap()).unwrap(),
                        ))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(fields.len(), case.fields.len(), "{}", case.name);
                let class_name = source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::ClassDeclaration(class) = &record.data else {
                            return None;
                        };
                        Some(source.node_ref(class.name.unwrap()).unwrap())
                    })
                    .unwrap();
                let instance = queries.get_type_at_location(class_name).unwrap();
                assert_eq!(queries.type_to_string(instance).unwrap(), "Model");
                let mut symbols = Vec::new();
                for (index, (declaration, name, annotation, initializer)) in
                    fields.iter().enumerate()
                {
                    let symbol = queries.get_symbol_at_location(*name).unwrap().unwrap();
                    let type_ = queries.get_type_at_location(*name).unwrap();
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                type_,
                                *declaration,
                                CanonicalTypeFormatFlags::NO_TRUNCATION
                                    | CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                            )
                            .unwrap(),
                        case.fields[index].0,
                        "{}, field {index}",
                        case.name
                    );
                    assert_eq!(queries.get_type_at_location(*declaration).unwrap(), type_);
                    for (previous, previous_symbol) in symbols.iter().enumerate() {
                        assert_eq!(
                            symbol == *previous_symbol,
                            case.fields[index].1 == case.fields[previous].1,
                            "{}, symbols {previous} and {index}",
                            case.name
                        );
                    }
                    symbols.push(symbol);
                    let NodeData::Identifier(identifier) = &program.node(*name).unwrap().data
                    else {
                        panic!("the control has an identifier property name")
                    };
                    assert_eq!(
                        queries
                            .symbol_to_string_at_location(symbol, *declaration)
                            .unwrap(),
                        format!("Model.{}", identifier.text)
                    );
                    let expected_declarations = fields
                        .iter()
                        .enumerate()
                        .filter_map(|(other, (declaration, _, _, _))| {
                            (case.fields[other].1 == case.fields[index].1).then_some(*declaration)
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(
                        queries.get_symbol_declarations(symbol).unwrap(),
                        expected_declarations
                    );
                    if let Some(annotation) = annotation {
                        let expected = match program.node(*annotation).unwrap().kind {
                            SyntaxKind::NumberKeyword => "number",
                            SyntaxKind::StringKeyword => "string",
                            _ => unreachable!(),
                        };
                        let annotation_type = queries.get_type_at_location(*annotation).unwrap();
                        assert_eq!(queries.type_to_string(annotation_type).unwrap(), expected);
                    }
                    let initializer_type = queries.get_type_at_location(*initializer).unwrap();
                    let expected = match &program.node(*initializer).unwrap().data {
                        NodeData::NumericLiteral(literal) => literal.text.clone(),
                        NodeData::StringLiteral(literal) => {
                            serde_json::to_string(&literal.text).unwrap()
                        }
                        _ => unreachable!(),
                    };
                    assert_eq!(queries.type_to_string(initializer_type).unwrap(), expected);
                    assert_eq!(queries.get_type_at_location(*name).unwrap(), type_);
                    assert_eq!(queries.get_symbol_at_location(*name).unwrap(), Some(symbol));
                }
                fields
                    .into_iter()
                    .map(|(declaration, name, _, _)| (declaration, name))
                    .collect::<Vec<_>>()
            },
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", case.name));
        let fields = fields.expect("the canonical checker must run");
        assert_eq!(
            program.diagnostics().len(),
            case.diagnostics.len(),
            "{}: {:?}",
            case.name,
            program.diagnostics()
        );
        for (diagnostic, &(code, field, message)) in
            program.diagnostics().iter().zip(case.diagnostics)
        {
            assert_eq!(diagnostic.code, Some(code), "{}", case.name);
            assert_eq!(diagnostic.message, message, "{}", case.name);
            assert_eq!(
                diagnostic.range,
                Some(program.node(fields[field].1).unwrap().range),
                "{}",
                case.name
            );
            if code == 2717 {
                let first = case
                    .fields
                    .iter()
                    .position(|candidate| candidate.1 == case.fields[field].1)
                    .unwrap();
                let [related] = diagnostic.related_information.as_slice() else {
                    panic!("the conflict points to the first declaration")
                };
                assert_eq!(related.code, Some(6203));
                assert_eq!(
                    related.range,
                    Some(program.node(fields[first].1).unwrap().range)
                );
                assert_eq!(related.message, "'value' was also declared here.");
            } else {
                assert!(diagnostic.related_information.is_empty());
            }
        }
    }
}
