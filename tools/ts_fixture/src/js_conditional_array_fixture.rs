use std::{fs, path::PathBuf};

use crate::{
    Case, FixtureChecker, compile_case_variant, expand_option_matrix, render_error_baseline,
};

const ORIGINAL: &str = concat!(
    "// @strict: true\n",
    "// @allowJs: true\n",
    "// @checkJs: true\n",
    "// @noEmit: true\n",
    "// @filename: t.js\n",
    "\n",
    "const is_morning = new Date().getHours() < 12;\n",
    "\n",
    "// prettier-ignore\n",
    "const greeting = ([\n",
    "  is_morning ? 'good morning' : 'good evening'\n",
    "]);\n",
);

#[test]
fn original_js_array_conditional_checks_date_and_both_branches() {
    let case = Case::parse(
        "testdata/tests/cases/compiler/jsSpeculativeParsingError.ts",
        ORIGINAL,
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, true).unwrap();
    let errors = render_error_baseline(&case, &compilation.diagnostics);
    if let Some(directory) = std::env::var_os("TS_JS_CONDITIONAL_ARRAY_ARTIFACT_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("original.ts"), ORIGINAL).unwrap();
        fs::write(directory.join("original.errors.txt"), &errors.text).unwrap();
        if let Some(artifacts) = &compilation.semantic_artifacts {
            match &artifacts.types {
                Ok(types) => fs::write(directory.join("original.types"), types).unwrap(),
                Err(error) => {
                    fs::write(directory.join("types-error.txt"), format!("{error:?}")).unwrap()
                }
            }
        }
    }
    assert!(errors.unsupported_details.is_empty());
    assert_eq!(errors.text, "");
    assert!(compilation.diagnostics.is_empty());
    let types = compilation
        .semantic_artifacts
        .as_ref()
        .unwrap()
        .types
        .as_ref()
        .unwrap();
    for expected in [
        ">Date : DateConstructor\r\n",
        ">new Date() : Date\r\n",
        ">new Date().getHours : () => number\r\n",
        ">new Date().getHours() : number\r\n",
        ">is_morning : boolean\r\n",
        ">greeting : string[]\r\n",
        ">is_morning ? 'good morning' : 'good evening' : \"good evening\" | \"good morning\"\r\n",
        ">'good morning' : \"good morning\"\r\n",
        ">'good evening' : \"good evening\"\r\n",
    ] {
        assert!(types.contains(expected), "missing {expected:?} in {types}");
    }
}

#[test]
fn js_array_conditional_checks_missing_names_in_both_branches() {
    let case = Case::parse(
        "jsArrayConditionalBranches.ts",
        concat!(
            "// @strict: true\n",
            "// @allowJs: true\n",
            "// @checkJs: true\n",
            "// @noEmit: true\n",
            "// @filename: branches.js\n",
            "const is_morning = new Date().getHours() < 12;\n",
            "const greeting = ([is_morning ? onlyTrueBranchMissing : onlyFalseBranchMissing]);\n",
        ),
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, false).unwrap();
    assert_eq!(
        compilation
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2304), Some(2304)]
    );
    assert_eq!(
        compilation.diagnostics[0].message,
        "Cannot find name 'onlyTrueBranchMissing'."
    );
    assert_eq!(
        compilation.diagnostics[1].message,
        "Cannot find name 'onlyFalseBranchMissing'."
    );
}

fn assert_contextual_conditional_array(
    name: &str,
    source: &str,
    expected_codes: &[u32],
    expected_types: &[&str],
) {
    let case = Case::parse(
        format!("contextualConditionalArray-{name}.ts"),
        format!(
            "// @strict: true\n// @target: es2015\n// @noEmit: true\n// @filename: input.ts\n{source}"
        ),
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, true).unwrap();
    let errors = render_error_baseline(&case, &compilation.diagnostics);
    let types = &compilation.semantic_artifacts.as_ref().unwrap().types;
    if let Some(directory) = std::env::var_os("TS_JS_CONDITIONAL_ARRAY_ARTIFACT_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join(format!("{name}.source.ts")), source).unwrap();
        fs::write(directory.join(format!("{name}.errors.txt")), &errors.text).unwrap();
        let diagnostics = compilation
            .diagnostics
            .iter()
            .map(|diagnostic| {
                serde_json::json!({"code": diagnostic.code, "message": diagnostic.message})
            })
            .collect::<Vec<_>>();
        fs::write(
            directory.join(format!("{name}.diagnostics.json")),
            serde_json::to_vec_pretty(&diagnostics).unwrap(),
        )
        .unwrap();
        match types {
            Ok(types) => fs::write(directory.join(format!("{name}.types")), types).unwrap(),
            Err(error) => fs::write(
                directory.join(format!("{name}.types-error.txt")),
                format!("{error:?}"),
            )
            .unwrap(),
        }
    }
    assert!(errors.unsupported_details.is_empty(), "{name}");
    assert_eq!(
        compilation
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        expected_codes.iter().copied().map(Some).collect::<Vec<_>>(),
        "{name}: {:?}",
        compilation.diagnostics,
    );
    let types = types.as_ref().unwrap();
    for &expected in expected_types {
        assert!(
            types.contains(expected),
            "{name}: missing {expected:?} in {types}"
        );
    }
}

#[test]
fn contextual_conditional_array_literals_keep_literal_types() {
    for (name, source, codes, types) in [
        (
            "literal-context",
            "const values: (\"a\" | \"b\")[] = [true ? \"a\" : \"b\"];\n",
            &[][..],
            &[
                ">[true ? \"a\" : \"b\"] : (\"a\" | \"b\")[]\r\n",
                ">true ? \"a\" : \"b\" : \"a\" | \"b\"\r\n",
            ][..],
        ),
        (
            "literal-wrong-branch",
            "const values: (\"a\" | \"b\")[] = [true ? \"a\" : 1];\n",
            &[2322][..],
            &[
                ">[true ? \"a\" : 1] : (\"a\" | 1)[]\r\n",
                ">true ? \"a\" : 1 : \"a\" | 1\r\n",
            ][..],
        ),
        (
            "literal-undefined",
            "const values: (\"a\" | \"b\")[] = [true ? \"a\" : undefined];\n",
            &[2322][..],
            &[
                ">[true ? \"a\" : undefined] : (\"a\" | undefined)[]\r\n",
                ">true ? \"a\" : undefined : \"a\" | undefined\r\n",
            ][..],
        ),
        (
            "literal-optional",
            "const values: (\"a\" | \"b\" | undefined)[] = [true ? \"a\" : undefined];\n",
            &[][..],
            &[
                ">[true ? \"a\" : undefined] : (\"a\" | undefined)[]\r\n",
                ">true ? \"a\" : undefined : \"a\" | undefined\r\n",
            ][..],
        ),
    ] {
        assert_contextual_conditional_array(name, source, codes, types);
    }
}

#[test]
fn contextual_conditional_arrays_check_variable_conditions() {
    for (name, source, codes, types) in [
        (
            "variable-context",
            "declare const flag: boolean;\nconst values: string[] = [flag ? \"a\" : \"b\"];\n",
            &[][..],
            &[
                ">[flag ? \"a\" : \"b\"] : string[]\r\n",
                ">flag ? \"a\" : \"b\" : \"a\" | \"b\"\r\n",
            ][..],
        ),
        (
            "variable-literal-context",
            "declare const flag: boolean;\nconst values: (\"a\" | \"b\")[] = [flag ? \"a\" : \"b\"];\n",
            &[][..],
            &[
                ">[flag ? \"a\" : \"b\"] : (\"a\" | \"b\")[]\r\n",
                ">flag ? \"a\" : \"b\" : \"a\" | \"b\"\r\n",
            ][..],
        ),
        (
            "variable-wrong-branch",
            "declare const flag: boolean;\nconst values: string[] = [flag ? \"a\" : 1];\n",
            &[2322][..],
            &[
                ">[flag ? \"a\" : 1] : (string | number)[]\r\n",
                ">flag ? \"a\" : 1 : \"a\" | 1\r\n",
            ][..],
        ),
        (
            "variable-undefined",
            "declare const flag: boolean;\nconst values: string[] = [flag ? \"a\" : undefined];\n",
            &[2322][..],
            &[
                ">[flag ? \"a\" : undefined] : (string | undefined)[]\r\n",
                ">flag ? \"a\" : undefined : \"a\" | undefined\r\n",
            ][..],
        ),
        (
            "variable-optional",
            "declare const flag: boolean;\nconst values: (string | undefined)[] = [flag ? \"a\" : undefined];\n",
            &[][..],
            &[
                ">[flag ? \"a\" : undefined] : (string | undefined)[]\r\n",
                ">flag ? \"a\" : undefined : \"a\" | undefined\r\n",
            ][..],
        ),
    ] {
        assert_contextual_conditional_array(name, source, codes, types);
    }
}

#[test]
fn contextual_conditional_arrays_keep_nested_object_context() {
    for (name, source) in [
        (
            "nested-object-true",
            "const values: { kind: \"a\" | \"b\" }[] = [true ? (true ? { kind: \"a\" } : { kind: \"b\" }) : { kind: \"a\" }];",
        ),
        (
            "nested-object-false",
            "const values: { kind: \"a\" | \"b\" }[] = [true ? { kind: \"a\" } : (true ? { kind: \"a\" } : { kind: \"b\" })];",
        ),
    ] {
        assert_contextual_conditional_array(
            name,
            source,
            &[],
            &[
                ">{ kind: \"a\" } : { kind: \"a\"; }\r\n",
                ">{ kind: \"b\" } : { kind: \"b\"; }\r\n",
            ],
        );
    }
}

#[test]
fn contextual_conditional_arrays_keep_nested_literal_types() {
    for (name, source) in [
        (
            "nested-literal-true",
            "const values: (\"a\" | \"b\")[] = [true ? (true ? \"a\" : \"b\") : \"a\"];",
        ),
        (
            "nested-literal-false",
            "const values: (\"a\" | \"b\")[] = [true ? \"a\" : (true ? \"a\" : \"b\")];",
        ),
    ] {
        assert_contextual_conditional_array(
            name,
            source,
            &[],
            &[
                ">values : (\"a\" | \"b\")[]\r\n",
                ">true ? \"a\" : \"b\" : \"a\" | \"b\"\r\n",
                ">(true ? \"a\" : \"b\") : \"a\" | \"b\"\r\n",
            ],
        );
    }
}

#[test]
fn contextual_conditional_arrays_check_nested_object_types() {
    for (name, source) in [
        (
            "nested-object-wrong-true",
            "const values: { kind: \"a\" | \"b\" }[] = [true ? (true ? { kind: \"a\" } : { kind: \"c\" }) : { kind: \"a\" }];",
        ),
        (
            "nested-object-wrong-false",
            "const values: { kind: \"a\" | \"b\" }[] = [true ? { kind: \"a\" } : (true ? { kind: \"c\" } : { kind: \"b\" })];",
        ),
    ] {
        assert_contextual_conditional_array(name, source, &[2322], &[]);
    }
}

#[test]
fn contextual_conditional_initializers_keep_literal_types() {
    for (name, source, codes) in [
        (
            "direct-nested-literal-context",
            "const value: \"a\" | \"b\" = true ? (true ? \"a\" : \"b\") : (false ? \"a\" : \"b\");",
            &[][..],
        ),
        (
            "direct-literal-context",
            "const value: \"a\" | \"b\" = true ? \"a\" : \"b\";",
            &[][..],
        ),
        (
            "direct-nested-true",
            "const value: \"a\" | \"b\" = true ? (true ? \"a\" : \"b\") : \"a\";",
            &[][..],
        ),
        (
            "direct-nested-false",
            "const value: \"a\" | \"b\" = true ? \"a\" : (false ? \"a\" : \"b\");",
            &[][..],
        ),
        (
            "direct-nested-wrong-literal",
            "const value: \"a\" | \"b\" = true ? (true ? \"a\" : \"b\") : (false ? \"a\" : \"c\");",
            &[2322][..],
        ),
        (
            "direct-wrong-literal",
            "const value: \"a\" | \"b\" = true ? \"a\" : \"c\";",
            &[2322][..],
        ),
    ] {
        assert_contextual_conditional_array(name, source, codes, &[">value : \"a\" | \"b\"\r\n"]);
    }
}

#[test]
fn contextual_conditional_initializers_keep_mixed_literal_types() {
    for (name, source, codes) in [
        (
            "direct-mixed-literals",
            "const value: \"a\" | 1 = true ? \"a\" : 1;",
            &[][..],
        ),
        (
            "direct-mixed-nested-true",
            "const value: \"a\" | 1 = true ? (true ? \"a\" : 1) : \"a\";",
            &[][..],
        ),
        (
            "direct-mixed-nested-false",
            "const value: \"a\" | 1 = true ? \"a\" : (false ? \"a\" : 1);",
            &[][..],
        ),
        (
            "direct-mixed-wrong-literal",
            "const value: \"a\" | 1 = true ? (true ? \"a\" : 1) : (false ? \"a\" : 2);",
            &[2322][..],
        ),
    ] {
        assert_contextual_conditional_array(name, source, codes, &[">value : \"a\" | 1\r\n"]);
    }
}

#[test]
fn contextual_conditional_initializers_keep_object_intersection_errors() {
    let case = Case::parse(
        "contextualConditionalObjectIntersection.ts",
        concat!(
            "// @strict: true\n",
            "// @target: es2015\n",
            "// @noEmit: true\n",
            "// @filename: input.ts\n",
            "const value: { a: number } & { b: string } = true ? \"a\" : \"b\";",
        ),
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, false).unwrap();
    let errors = render_error_baseline(&case, &compilation.diagnostics);
    assert!(errors.unsupported_details.is_empty());
    let [diagnostic] = compilation.diagnostics.as_slice() else {
        panic!("expected one intersection assignment diagnostic")
    };
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(
        diagnostic
            .range
            .map(|range| (range.start.get(), range.end.get())),
        Some((6, 11))
    );
    assert_eq!(
        diagnostic.message,
        "Type 'string' is not assignable to type '{ a: number; } & { b: string; }'.",
    );
}
