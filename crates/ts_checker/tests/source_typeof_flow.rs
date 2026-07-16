use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "type Shape = { value: number };\n",
    "type Handler = (value: number) => number;\n",
    "function stringCase(value: string | number): string | number {\n",
    "  if (typeof value === \"string\") {\n",
    "    const stringSelected: string = value;\n",
    "    return stringSelected;\n",
    "  } else {\n",
    "    const stringRejected: number = value;\n",
    "    return stringRejected;\n",
    "  }\n",
    "}\n",
    "function numberCase(value: string | number): string | number {\n",
    "  if (typeof value !== \"number\") {\n",
    "    const numberRejected: string = value;\n",
    "    return numberRejected;\n",
    "  } else {\n",
    "    const numberSelected: number = value;\n",
    "    return numberSelected;\n",
    "  }\n",
    "}\n",
    "function booleanCase(value: boolean | number): boolean | number {\n",
    "  if (\"boolean\" !== typeof value) {\n",
    "    const booleanRejected: number = value;\n",
    "    return booleanRejected;\n",
    "  } else {\n",
    "    const booleanSelected: boolean = value;\n",
    "    return booleanSelected;\n",
    "  }\n",
    "}\n",
    "function bigintCase(value: bigint | string): bigint | string {\n",
    "  if (\"bigint\" === typeof value) {\n",
    "    const bigintSelected: bigint = value;\n",
    "    return bigintSelected;\n",
    "  } else {\n",
    "    const bigintRejected: string = value;\n",
    "    return bigintRejected;\n",
    "  }\n",
    "}\n",
    "function symbolCase(value: symbol | string): symbol | string {\n",
    "  if (typeof value === \"symbol\") {\n",
    "    const symbolSelected: symbol = value;\n",
    "    return symbolSelected;\n",
    "  } else {\n",
    "    const symbolRejected: string = value;\n",
    "    return symbolRejected;\n",
    "  }\n",
    "}\n",
    "function undefinedCase(value: undefined | string): undefined | string {\n",
    "  if (typeof value !== \"undefined\") {\n",
    "    const undefinedRejected: string = value;\n",
    "    return undefinedRejected;\n",
    "  } else {\n",
    "    const undefinedSelected: undefined = value;\n",
    "    return undefinedSelected;\n",
    "  }\n",
    "}\n",
    "function objectCase(value: Shape | null | Handler): Shape | null | Handler {\n",
    "  if (typeof value === \"object\") {\n",
    "    const objectSelected: Shape | null = value;\n",
    "    return objectSelected;\n",
    "  } else {\n",
    "    const objectRejected: Handler = value;\n",
    "    return objectRejected;\n",
    "  }\n",
    "}\n",
    "function functionCase(value: Shape | null | Handler): Shape | null | Handler {\n",
    "  if (\"function\" !== typeof value) {\n",
    "    const functionRejected: Shape | null = value;\n",
    "    return functionRejected;\n",
    "  } else {\n",
    "    const functionSelected: Handler = value;\n",
    "    return functionSelected;\n",
    "  }\n",
    "}\n",
    "function joinedCase(value: string | number): string | number {\n",
    "  if (typeof value === \"string\") {\n",
    "    const joinedString: string = value;\n",
    "  } else {\n",
    "    const joinedNumber: number = value;\n",
    "  }\n",
    "  const joinedAfter: string | number = value;\n",
    "  return joinedAfter;\n",
    "}\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/source-typeof-flow.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.initializer.expect("expected initialized variable"),
                )
            })
        })
        .unwrap_or_else(|| panic!("expected one variable named {expected:?}"))
}

fn rendered_initializer_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    variable: &str,
) -> String {
    context
        .type_to_string(resolved_type(
            context,
            variable_initializer(parsed, file, variable),
        ))
        .unwrap()
}

#[test]
fn strict_typeof_flow_narrows_all_tags_joins_and_replays_warm() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_301);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for (variable, expected) in [
        ("stringSelected", "string"),
        ("stringRejected", "number"),
        ("numberSelected", "number"),
        ("numberRejected", "string"),
        ("booleanSelected", "boolean"),
        ("booleanRejected", "number"),
        ("bigintSelected", "bigint"),
        ("bigintRejected", "string"),
        ("symbolSelected", "symbol"),
        ("symbolRejected", "string"),
        ("undefinedSelected", "undefined"),
        ("undefinedRejected", "string"),
        ("joinedString", "string"),
        ("joinedNumber", "number"),
        ("joinedAfter", "string | number"),
    ] {
        assert_eq!(
            rendered_initializer_type(&context, &parsed, file, variable),
            expected,
            "unexpected flow type for {variable}",
        );
    }

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let typeof_type = bootstrap.typeof_type;
    let boolean_type = bootstrap.boolean_type;
    let mut typeof_count = 0;
    let mut comparison_count = 0;
    for (node, record) in parsed.arena.iter() {
        let node = NodeRef::new(parsed.arena.id(), file, node);
        match record.kind {
            SyntaxKind::TypeOfExpression => {
                assert_eq!(resolved_type(&context, node), typeof_type);
                typeof_count += 1;
            }
            SyntaxKind::BinaryExpression => {
                assert_eq!(resolved_type(&context, node), boolean_type);
                comparison_count += 1;
            }
            _ => {}
        }
    }
    assert_eq!(typeof_count, 9);
    assert_eq!(comparison_count, 9);

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}
