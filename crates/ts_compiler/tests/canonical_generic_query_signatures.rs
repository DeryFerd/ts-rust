use ts_ast::{NodeData, NodeRef};
use ts_compiler::{Program, SourceFile};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const FILE_NAME: &str = "/project/generic-query-signatures.ts";

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

struct FunctionNodes {
    declaration: NodeRef,
    name: NodeRef,
    type_parameters: Vec<(NodeRef, NodeRef)>,
    parameter: NodeRef,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    annotations: Vec<NodeRef>,
}

fn function_nodes(source: &SourceFile, expected: &str) -> FunctionNodes {
    let node_ref = |node| source.node_ref(node).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &source.parse.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            let mut annotations = Vec::new();
            let type_parameters = function
                .type_parameters
                .as_ref()?
                .nodes
                .iter()
                .map(|&node| {
                    let NodeData::TypeParameterDeclaration(parameter) =
                        &source.parse.arena.get(node).unwrap().data
                    else {
                        panic!("expected a type parameter")
                    };
                    annotations.extend(
                        [parameter.constraint, parameter.default_type]
                            .into_iter()
                            .flatten()
                            .map(node_ref),
                    );
                    (node_ref(node), node_ref(parameter.name))
                })
                .collect();
            let parameter_node = function.parameters.nodes[0];
            let NodeData::ParameterDeclaration(parameter) =
                &source.parse.arena.get(parameter_node).unwrap().data
            else {
                panic!("expected a value parameter")
            };
            let parameter_annotation = node_ref(parameter.type_?);
            let return_annotation = node_ref(function.type_?);
            annotations.extend([parameter_annotation, return_annotation]);
            Some(FunctionNodes {
                declaration: node_ref(node),
                name: node_ref(name),
                type_parameters,
                parameter: node_ref(parameter.name),
                parameter_annotation,
                return_annotation,
                annotations,
            })
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

#[allow(clippy::too_many_lines)] // Keep the public query identities and their replay together.
fn check_declaration(
    source: &str,
    name: &str,
    parameter_names: &[&str],
    return_parameter: Option<usize>,
) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, source).unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["generic-query-signatures.ts".to_owned()],
        options(),
        |program, queries| {
            let function = function_nodes(program.source_file(FILE_NAME).unwrap(), name);
            assert_eq!(function.type_parameters.len(), parameter_names.len());
            let callable = queries.get_type_at_location(function.name).unwrap();
            assert_eq!(
                queries.get_type_at_location(function.declaration).unwrap(),
                callable,
            );
            let owner = queries
                .get_symbol_at_location(function.name)
                .unwrap()
                .unwrap();
            assert_eq!(
                queries.get_symbol_declarations(owner).unwrap(),
                [function.declaration],
            );
            let type_parameters = function
                .type_parameters
                .iter()
                .zip(parameter_names)
                .map(|(&(declaration, name), expected)| {
                    let symbol = queries.get_symbol_at_location(name).unwrap().unwrap();
                    assert_eq!(
                        queries.get_symbol_declarations(symbol).unwrap(),
                        [declaration],
                    );
                    assert_eq!(queries.symbol_to_string(symbol).unwrap(), *expected);
                    queries.get_type_at_location(name).unwrap()
                })
                .collect::<Vec<_>>();
            for (index, type_) in type_parameters.iter().enumerate() {
                assert!(!type_parameters[..index].contains(type_));
            }
            let parameter = queries.get_type_at_location(function.parameter).unwrap();
            assert_eq!(
                queries
                    .get_type_at_location(function.parameter_annotation)
                    .unwrap(),
                parameter,
            );
            let returned = queries
                .get_type_at_location(function.return_annotation)
                .unwrap();
            assert_eq!(parameter, returned);
            if let Some(index) = return_parameter {
                assert_eq!(returned, type_parameters[index]);
            } else {
                assert!(!type_parameters.contains(&returned));
            }
            let locations = [function.declaration, function.name, function.parameter]
                .into_iter()
                .chain(
                    function
                        .type_parameters
                        .iter()
                        .flat_map(|&(declaration, name)| [declaration, name]),
                )
                .chain(function.annotations)
                .collect::<Vec<_>>();
            let identities = locations
                .iter()
                .map(|&node| {
                    (
                        node,
                        queries.get_type_at_location(node).unwrap(),
                        queries.get_symbol_at_location(node).unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{cold:?}");
            let store = queries.semantic_store_id();
            assert_eq!(queries.replay_sources().unwrap(), cold);
            for (node, type_, symbol) in identities {
                assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
                assert_eq!(queries.get_symbol_at_location(node).unwrap(), symbol);
            }
            assert_eq!(queries.semantic_store_id(), store);
        },
    )
    .unwrap();
    result.expect("canonical checker ran");
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics(),
    );
}

#[test]
fn forward_bound_keeps_later_parameter_artifacts() {
    check_declaration(
        "declare function forward<T extends U, U>(value: T): T;",
        "forward",
        &["T", "U"],
        Some(0),
    );
}

#[test]
fn union_alias_bound_keeps_parameter_artifacts() {
    check_declaration(
        "type StringOr<T> = T | string; declare function union<B, T extends StringOr<B>>(value: T): T;",
        "union",
        &["B", "T"],
        Some(1),
    );
}

#[test]
fn keyof_bound_keeps_parameter_artifacts() {
    check_declaration(
        "declare function key<O, K extends keyof O>(value: K): K;",
        "key",
        &["O", "K"],
        Some(1),
    );
}

#[test]
fn object_alias_annotations_keep_the_same_type_in_the_body() {
    check_declaration(
        "type Box<T> = { value: T }; function keep<T>(value: Box<T>): Box<T> { return value; }",
        "keep",
        &["T"],
        None,
    );
}

#[test]
fn array_default_declaration_uses_the_bundled_array_type() {
    check_declaration(
        "declare function arrays<T, U extends T[] = T[]>(value: U): U;",
        "arrays",
        &["T", "U"],
        Some(1),
    );
}

#[test]
fn array_default_call_keeps_number_array_artifacts_after_replay() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            FILE_NAME,
            concat!(
                "declare function arrays<T, U extends T[] = T[]>(value: U): U;\n",
                "const numbers: number[] = arrays<number>([1, 2]);\n",
            ),
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["generic-query-signatures.ts".to_owned()],
        options(),
        |program, queries| {
            let source = program.source_file(FILE_NAME).unwrap();
            let (variable, name, annotation, call) = source
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    Some((
                        source.node_ref(node).unwrap(),
                        source.node_ref(variable.name).unwrap(),
                        source.node_ref(variable.type_?).unwrap(),
                        source.node_ref(variable.initializer?).unwrap(),
                    ))
                })
                .unwrap();
            let expected = queries.get_type_at_location(annotation).unwrap();
            assert_eq!(queries.type_to_string(expected).unwrap(), "number[]");
            let owner = queries.get_symbol_at_location(name).unwrap().unwrap();
            assert_eq!(queries.get_symbol_declarations(owner).unwrap(), [variable]);
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{cold:?}");
            for replay in [false, true] {
                if replay {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                }
                for node in [name, annotation, call] {
                    assert_eq!(queries.get_type_at_location(node).unwrap(), expected);
                }
                assert_eq!(queries.get_symbol_at_location(name).unwrap(), Some(owner));
            }
        },
    )
    .unwrap();
    result.expect("canonical checker ran");
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics(),
    );
}

fn span_within(source: &str, container: &str, selected: &str) -> (u32, u32) {
    let start = source.find(container).unwrap() + container.find(selected).unwrap();
    (
        u32::try_from(start).unwrap(),
        u32::try_from(start + selected.len()).unwrap(),
    )
}

fn check_diagnostics(source: &str, expected: &[(u32, &str, &str, &str)]) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, source).unwrap();
    let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["generic-query-signatures.ts".to_owned()],
        options(),
        |_, queries| queries.replay_sources().unwrap(),
    )
    .unwrap();
    assert_eq!(program.diagnostics(), replay.unwrap());
    assert_eq!(
        program.diagnostics().len(),
        expected.len(),
        "{:?}",
        program.diagnostics(),
    );
    for (diagnostic, &(code, message, container, selected)) in
        program.diagnostics().iter().zip(expected)
    {
        assert_eq!(diagnostic.file_name.as_deref(), Some(FILE_NAME));
        assert_eq!(diagnostic.code, Some(code));
        assert_eq!(diagnostic.message, message);
        let range = diagnostic.range.unwrap();
        assert_eq!(
            (range.start.get(), range.end.get()),
            span_within(source, container, selected),
        );
    }
}

#[test]
fn invalid_default_reports_the_pinned_constraint_diagnostic() {
    // Algorithm reference: typescript-go dc37b524, internal/checker/checker.go.
    // Pinned Go checkTypeParameter checks assignability at the default node.
    check_diagnostics(
        "declare function badDefault<T extends string = number>(value: T): T;",
        &[(
            2344,
            "Type 'number' does not satisfy the constraint 'string'.",
            "string = number",
            "number",
        )],
    );
}

#[test]
fn later_parameter_default_reports_the_pinned_reference_diagnostic() {
    // Pinned Go checkTypeParametersNotReferenced reports the reference node.
    check_diagnostics(
        "declare function forwardDefault<T = U, U = string>(value: T): T;",
        &[(
            2744,
            "Type parameter defaults can only reference previously declared type parameters.",
            "T = U",
            "U",
        )],
    );
}

#[test]
fn constraint_cycle_reports_the_pinned_diagnostics_at_both_bounds() {
    // Pinned Go getResolvedBaseConstraint reports each parameter's constraint node.
    check_diagnostics(
        "declare function circular<T extends U, U extends T>(value: T): T;",
        &[
            (
                2313,
                "Type parameter 'T' has a circular constraint.",
                "T extends U",
                "U",
            ),
            (
                2313,
                "Type parameter 'U' has a circular constraint.",
                "U extends T",
                "T",
            ),
        ],
    );
}
