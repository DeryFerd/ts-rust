use ts_ast::{NodeData, NodeRef};
use ts_checker::semantic::{SourceCheckError, UnsupportedSourceSyntax};
use ts_compiler::{CanonicalProgramCheckError, CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options() -> CompilerOptions {
    CompilerOptions {
        strict: true,
        no_emit: true,
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

fn identifiers(program: &Program, name: &str) -> Vec<NodeRef> {
    let source = program.source_file("/project/input.ts").unwrap();
    let mut nodes = source
        .parse
        .arena
        .iter()
        .filter_map(|(node, record)| match &record.data {
            NodeData::Identifier(identifier) if identifier.text == name => source.node_ref(node),
            _ => None,
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|node| source.parse.arena.get(node.node).unwrap().range.start);
    nodes
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the complete artifact checks and their replay together.
fn assertion_display_keeps_optional_value_types_call_results_and_symbols() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            concat!(
                "export function assertWeird(value?: string): asserts value {}\n",
                "assertWeird();\n",
                "assertWeird('hello');\n",
            ),
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options(),
        |program, queries| {
            let names = identifiers(program, "assertWeird");
            assert_eq!(names.len(), 3);
            let callable = queries.get_type_at_location(names[0]).unwrap();
            // Export declarations and local references retain separate symbol IDs.
            let symbols = names
                .iter()
                .map(|&location| queries.get_symbol_at_location(location).unwrap().unwrap())
                .collect::<Vec<_>>();
            let declarations = queries
                .get_symbol_declarations(symbols[0])
                .unwrap()
                .to_vec();
            assert_eq!(declarations.len(), 1);
            let value = identifiers(program, "value")[0];
            let value_type = queries.get_type_at_location(value).unwrap();
            let source = program.source_file("/project/input.ts").unwrap();
            let calls = source
                .parse
                .arena
                .iter()
                .filter(|(_, record)| matches!(record.data, NodeData::CallExpression(_)))
                .map(|(node, _)| source.node_ref(node).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(calls.len(), 2);
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty());
            let store = queries.semantic_store_id();
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                }
                for (&location, &symbol) in names.iter().zip(&symbols) {
                    assert_eq!(queries.get_type_at_location(location).unwrap(), callable);
                    assert_eq!(
                        queries.get_symbol_at_location(location).unwrap(),
                        Some(symbol),
                    );
                    assert_eq!(
                        queries.get_symbol_declarations(symbol).unwrap(),
                        declarations,
                    );
                    assert_eq!(
                        queries
                            .symbol_to_string_at_location(symbol, location)
                            .unwrap(),
                        "assertWeird",
                    );
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                callable,
                                location,
                                CanonicalTypeFormatFlags::NO_TRUNCATION,
                            )
                            .unwrap(),
                        "(value?: string) => asserts value",
                    );
                }
                assert_eq!(
                    queries.type_to_string(callable).unwrap(),
                    "(value?: string | undefined) => asserts value",
                );
                assert_eq!(queries.get_type_at_location(value).unwrap(), value_type);
                assert_eq!(
                    queries.type_to_string(value_type).unwrap(),
                    "string | undefined"
                );
                for &call in &calls {
                    let return_type = queries.get_type_at_location(call).unwrap();
                    assert_eq!(queries.type_to_string(return_type).unwrap(), "void");
                }
                assert_eq!(queries.semantic_store_id(), store);
            }
        },
    )
    .unwrap();
    result.expect("canonical checker ran");
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn predicate_display_uses_typed_source_and_function_type_signatures() {
    for (source, expected, context_free) in [
        (
            "export function check(value: unknown): value is string { return typeof value === 'string'; } check('hello');",
            "(value: unknown) => value is string",
            "(value: unknown) => value is string",
        ),
        (
            "export function check(value: unknown): asserts value is string {} check('hello');",
            "(value: unknown) => asserts value is string",
            "(value: unknown) => asserts value is string",
        ),
        (
            "export declare const check: (value?: string) => asserts value; check('hello');",
            "(value?: string) => asserts value",
            "(value?: string | undefined) => asserts value",
        ),
        (
            "export declare const check: (value: unknown) => value is string; check('hello');",
            "(value: unknown) => value is string",
            "(value: unknown) => value is string",
        ),
    ] {
        assert_signature_display(source, expected, context_free);
    }
}

#[test]
fn unadmitted_assertion_arrow_does_not_reach_artifact_queries() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            "export const check = (value?: string): asserts value => {};",
        )
        .unwrap();
    let mut queried = false;
    let result = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options(),
        |_, _| queried = true,
    );
    let Err(error) = result else {
        panic!("the unsupported arrow must stop before artifact queries");
    };
    assert!(matches!(
        error,
        CanonicalProgramCheckError::SourceCheck {
            error: SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(_)),
            ..
        }
    ));
    assert!(!queried);
}

#[test]
fn optional_signature_display_keeps_explicit_undefined_and_required_parameters() {
    for (source, expected, context_free) in [
        (
            "export function check(value?: string): void {}",
            "(value?: string) => void",
            "(value?: string | undefined) => void",
        ),
        (
            "export function check(value?: string | undefined): void {}",
            "(value?: string | undefined) => void",
            "(value?: string | undefined) => void",
        ),
        (
            "export function check(value: string | undefined): void {}",
            "(value: string | undefined) => void",
            "(value: string | undefined) => void",
        ),
        (
            "export function check(value: string = ''): void {}",
            "(value?: string) => void",
            "(value?: string) => void",
        ),
        (
            "export function check(value: string = '', next: number): void {}",
            "(value: string | undefined, next: number) => void",
            "(value: string | undefined, next: number) => void",
        ),
        (
            "export declare const check: (value?: string) => void; check();",
            "(value?: string) => void",
            "(value?: string | undefined) => void",
        ),
    ] {
        assert_signature_display(source, expected, context_free);
    }
}

fn assert_signature_display(source: &str, expected: &str, context_free: &str) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options(),
        |program, queries| {
            let names = identifiers(program, "check");
            let callable = queries.get_type_at_location(names[0]).unwrap();
            let symbols = names
                .iter()
                .map(|&location| queries.get_symbol_at_location(location).unwrap().unwrap())
                .collect::<Vec<_>>();
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{source}: {cold:?}");
            let store = queries.semantic_store_id();
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold, "{source}");
                }
                for (&location, &symbol) in names.iter().zip(&symbols) {
                    assert_eq!(queries.get_type_at_location(location).unwrap(), callable);
                    assert_eq!(
                        queries.get_symbol_at_location(location).unwrap(),
                        Some(symbol),
                    );
                    assert_eq!(
                        queries
                            .symbol_to_string_at_location(symbol, location)
                            .unwrap(),
                        "check",
                    );
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                callable,
                                location,
                                CanonicalTypeFormatFlags::NO_TRUNCATION,
                            )
                            .unwrap(),
                        expected,
                        "{source}",
                    );
                }
                assert_eq!(
                    queries.type_to_string(callable).unwrap(),
                    context_free,
                    "{source}"
                );
                assert_eq!(queries.semantic_store_id(), store);
            }
        },
    )
    .unwrap();
    result.expect("canonical checker ran");
    assert!(
        program.diagnostics().is_empty(),
        "{source}: {:?}",
        program.diagnostics()
    );
}
