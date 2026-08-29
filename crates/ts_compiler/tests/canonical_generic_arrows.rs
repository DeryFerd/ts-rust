use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalProgramQueries, CanonicalTypeId, Program, SourceFile};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const FILE_NAME: &str = "/project/arrows.ts";

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

struct ArrowNodes {
    declaration: NodeRef,
    value_declaration: NodeRef,
    value_name: Option<NodeRef>,
    type_parameters: Vec<(NodeRef, NodeRef)>,
    parameters: Vec<(NodeRef, NodeRef)>,
    annotations: Vec<NodeRef>,
    return_annotation: NodeRef,
    body_expression: NodeRef,
}

fn arrow_nodes(source: &SourceFile) -> ArrowNodes {
    let node_ref = |node| source.node_ref(node).unwrap();
    let arrows = source
        .parse
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
        panic!("the source must contain one actual ArrowFunction")
    };
    let value_declaration = node_ref(record.parent.unwrap());
    let value_name = match &source.parse.arena.get(value_declaration.node).unwrap().data {
        NodeData::VariableDeclaration(variable) => Some(node_ref(variable.name)),
        NodeData::ExportAssignment(export) => {
            assert!(!export.is_export_equals);
            assert_eq!(export.expression, *node);
            None
        }
        _ => panic!("expected a variable or direct default export"),
    };
    let mut annotations = Vec::new();
    let type_parameters = arrow
        .type_parameters
        .as_ref()
        .into_iter()
        .flat_map(|parameters| &parameters.nodes)
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
    let parameters = arrow
        .parameters
        .nodes
        .iter()
        .map(|&node| {
            let NodeData::ParameterDeclaration(parameter) =
                &source.parse.arena.get(node).unwrap().data
            else {
                panic!("expected a typed parameter")
            };
            let annotation = node_ref(parameter.type_.unwrap());
            annotations.push(annotation);
            (node_ref(parameter.name), annotation)
        })
        .collect();
    let return_annotation = node_ref(arrow.type_.unwrap());
    annotations.push(return_annotation);
    let body_expression = match &source.parse.arena.get(arrow.body).unwrap().data {
        NodeData::Block(block) => {
            let [statement] = block.statements.nodes.as_slice() else {
                panic!("expected one return")
            };
            let NodeData::ReturnStatement(returned) =
                &source.parse.arena.get(*statement).unwrap().data
            else {
                panic!("expected a return statement")
            };
            node_ref(returned.expression.unwrap())
        }
        _ => node_ref(arrow.body),
    };
    ArrowNodes {
        declaration: node_ref(*node),
        value_declaration,
        value_name,
        type_parameters,
        parameters,
        annotations,
        return_annotation,
        body_expression,
    }
}

fn call_result_locations(source: &SourceFile) -> Vec<(NodeRef, NodeRef, NodeRef)> {
    source
        .parse
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let initializer = variable.initializer?;
            if !matches!(
                source.parse.arena.get(initializer)?.data,
                NodeData::CallExpression(_)
            ) {
                return None;
            }
            Some((
                source.node_ref(variable.name).unwrap(),
                source.node_ref(variable.type_?).unwrap(),
                source.node_ref(initializer).unwrap(),
            ))
        })
        .collect()
}

fn check_call_results(
    queries: &mut CanonicalProgramQueries<'_>,
    locations: &[(NodeRef, NodeRef, NodeRef)],
) -> Vec<(CanonicalTypeId, CanonicalTypeId)> {
    locations
        .iter()
        .map(|&(name, annotation, call)| {
            let expected = queries.get_type_at_location(annotation).unwrap();
            let actual = queries.get_type_at_location(call).unwrap();
            assert_eq!(queries.get_type_at_location(name).unwrap(), expected);
            // Literal inference can retain a fresh type while the annotation is regular.
            assert_eq!(
                queries.type_to_string(actual).unwrap(),
                queries.type_to_string(expected).unwrap()
            );
            (expected, actual)
        })
        .collect()
}

#[allow(clippy::too_many_lines)] // Keep the complete public identity and replay checks together.
fn check_arrow(source: &str, parameter_names: &[&str], return_parameter: Option<usize>) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, source).unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["arrows.ts".to_owned()],
        options(),
        |program, queries| {
            let source = program.source_file(FILE_NAME).unwrap();
            let arrow = arrow_nodes(source);
            let callable = queries.get_type_at_location(arrow.declaration).unwrap();
            // Expression queries have no public symbol. Checker tests inspect the binder owner.
            assert_eq!(
                queries.get_symbol_at_location(arrow.declaration).unwrap(),
                None
            );
            if let Some(name) = arrow.value_name {
                assert_eq!(queries.get_type_at_location(name).unwrap(), callable);
                let variable = queries.get_symbol_at_location(name).unwrap().unwrap();
                assert_eq!(
                    queries.get_symbol_declarations(variable).unwrap(),
                    [arrow.value_declaration]
                );
            }
            assert_eq!(arrow.type_parameters.len(), parameter_names.len());
            let type_parameters = arrow
                .type_parameters
                .iter()
                .zip(parameter_names)
                .map(|(&(declaration, name), expected)| {
                    let symbol = queries.get_symbol_at_location(name).unwrap().unwrap();
                    assert_eq!(
                        queries.get_symbol_declarations(symbol).unwrap(),
                        [declaration]
                    );
                    assert_eq!(queries.symbol_to_string(symbol).unwrap(), *expected);
                    let type_ = queries.get_type_at_location(name).unwrap();
                    assert_eq!(queries.type_to_string(type_).unwrap(), *expected);
                    type_
                })
                .collect::<Vec<_>>();
            for (index, type_) in type_parameters.iter().enumerate() {
                assert!(!type_parameters[..index].contains(type_));
            }
            let returned = queries
                .get_type_at_location(arrow.return_annotation)
                .unwrap();
            let body = queries.get_type_at_location(arrow.body_expression).unwrap();
            if let Some(index) = return_parameter {
                assert_eq!(returned, type_parameters[index]);
            } else {
                assert!(!type_parameters.contains(&returned));
            }
            if let Some(&(name, annotation)) = arrow.parameters.first() {
                assert_eq!(queries.get_type_at_location(name).unwrap(), returned);
                assert_eq!(queries.get_type_at_location(annotation).unwrap(), returned);
                assert_eq!(body, returned);
                assert_eq!(
                    queries
                        .get_symbol_at_location(arrow.body_expression)
                        .unwrap(),
                    queries.get_symbol_at_location(name).unwrap()
                );
            } else {
                assert_eq!(queries.type_to_string(returned).unwrap(), "number");
                assert_eq!(queries.type_to_string(body).unwrap(), "1");
            }
            let locations = [arrow.declaration, arrow.body_expression]
                .into_iter()
                .chain(arrow.value_name)
                .chain(
                    arrow
                        .type_parameters
                        .iter()
                        .flat_map(|&(declaration, name)| [declaration, name]),
                )
                .chain(arrow.parameters.iter().map(|&(name, _)| name))
                .chain(arrow.annotations)
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
            let call_locations = call_result_locations(source);
            let calls = check_call_results(queries, &call_locations);
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{cold:?}");
            let store = queries.semantic_store_id();
            assert_eq!(queries.replay_sources().unwrap(), cold);
            for (node, type_, symbol) in identities {
                assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
                assert_eq!(queries.get_symbol_at_location(node).unwrap(), symbol);
            }
            assert_eq!(check_call_results(queries, &call_locations), calls);
            assert_eq!(queries.semantic_store_id(), store);
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
fn generic_arrow_identity_calls_keep_public_type_and_symbol_ids() {
    check_arrow(
        concat!(
            "const keep = <T>(value: T): T => value;\n",
            "const explicit: number = keep<number>(1);\n",
            "const inferred: 'kept' = keep('kept');\n",
        ),
        &["T"],
        Some(0),
    );
}

#[test]
fn generic_arrow_single_return_block_keeps_public_parameter_identity() {
    check_arrow(
        "const keep = <T>(value: T): T => { return value; };",
        &["T"],
        Some(0),
    );
}

#[test]
fn generic_arrow_zero_parameters_keep_the_written_return_type() {
    check_arrow("const make = <T>(): number => 1;", &["T"], None);
}

#[test]
fn generic_arrow_interface_annotations_keep_the_same_public_type() {
    // This new interface control leaves the existing Box type-alias tests unchanged.
    check_arrow(
        "interface Box<T> { value: T } const keepBox = <T>(value: Box<T>): Box<T> => { return value; };",
        &["T"],
        None,
    );
}

#[test]
fn generic_arrow_array_defaults_use_the_bundled_library() {
    check_arrow(
        "const defaults = <T, U extends T[] = T[]>(value: U): U => value;",
        &["T", "U"],
        Some(1),
    );
}

fn span_within(source: &str, container: &str, selected: &str) -> (u32, u32) {
    let start = source.find(container).unwrap() + container.find(selected).unwrap();
    (
        u32::try_from(start).unwrap(),
        u32::try_from(start + selected.len()).unwrap(),
    )
}

fn check_diagnostic(source: &str, code: u32, message: &str, container: &str, selected: &str) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, source).unwrap();
    let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["arrows.ts".to_owned()],
        options(),
        |_, queries| queries.replay_sources().unwrap(),
    )
    .unwrap();
    assert_eq!(program.diagnostics(), replay.unwrap());
    let [diagnostic] = program.diagnostics() else {
        panic!("expected one diagnostic: {:?}", program.diagnostics())
    };
    assert_eq!(diagnostic.file_name.as_deref(), Some(FILE_NAME));
    assert_eq!(diagnostic.code, Some(code));
    assert_eq!(diagnostic.message, message);
    let range = diagnostic.range.unwrap();
    assert_eq!(
        (range.start.get(), range.end.get()),
        span_within(source, container, selected)
    );
}

#[test]
fn generic_arrow_invalid_body_reports_2322_at_the_expression() {
    check_diagnostic(
        "const bad = <T>(): string => 1;",
        2322,
        "Type 'number' is not assignable to type 'string'.",
        "=> 1",
        "1",
    );
}

#[test]
fn generic_arrow_self_constraint_reports_2313_at_the_constraint() {
    check_diagnostic(
        "const circular = <T extends T>(value: T): T => value;",
        2313,
        "Type parameter 'T' has a circular constraint.",
        "extends T",
        "T",
    );
}

#[test]
fn generic_arrow_invalid_default_reports_2344_at_the_default() {
    check_diagnostic(
        "const bad = <T extends string = number>(): string => '';",
        2344,
        "Type 'number' does not satisfy the constraint 'string'.",
        "string = number",
        "number",
    );
}

fn check_default_import(provider_text: &str, importer_text: &str) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/provider.ts", provider_text)
        .unwrap();
    filesystem
        .write_file("/project/importer.ts", importer_text)
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["importer.ts".to_owned()],
        options(),
        |program, queries| {
            // Program checks dependencies before this callback. Source-order controls live in ts_checker.
            let provider = program.source_file("/project/provider.ts").unwrap();
            let importer = program.source_file("/project/importer.ts").unwrap();
            let arrow = arrow_nodes(provider);
            let (clause, imported_name) = importer
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ImportClause(clause) = &record.data else {
                        return None;
                    };
                    Some((
                        importer.node_ref(node).unwrap(),
                        importer.node_ref(clause.name?).unwrap(),
                    ))
                })
                .unwrap();
            let callable = queries.get_type_at_location(arrow.declaration).unwrap();
            assert_eq!(
                queries.get_type_at_location(imported_name).unwrap(),
                callable
            );
            assert_eq!(
                queries.get_symbol_at_location(arrow.declaration).unwrap(),
                None
            );
            let alias = queries
                .get_symbol_at_location(imported_name)
                .unwrap()
                .unwrap();
            assert_eq!(queries.get_symbol_declarations(alias).unwrap(), [clause]);
            let mut locations = vec![
                arrow.declaration,
                arrow.return_annotation,
                arrow.body_expression,
                imported_name,
            ];
            locations.extend(
                arrow
                    .type_parameters
                    .iter()
                    .flat_map(|&(declaration, name)| [declaration, name]),
            );
            locations.extend(
                arrow
                    .parameters
                    .iter()
                    .flat_map(|&(name, annotation)| [name, annotation]),
            );
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
            let calls = call_result_locations(importer);
            let call_types = check_call_results(queries, &calls);
            assert!(!calls.is_empty());
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{cold:?}");
            let store = queries.semantic_store_id();
            assert_eq!(queries.replay_sources().unwrap(), cold);
            for (node, type_, symbol) in identities {
                assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
                assert_eq!(queries.get_symbol_at_location(node).unwrap(), symbol);
            }
            assert_eq!(check_call_results(queries, &calls), call_types);
            assert_eq!(queries.semantic_store_id(), store);
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
fn direct_default_nongeneric_arrow_imports_and_calls_keep_public_ids() {
    check_default_import(
        "export default (value: number): number => value;",
        "import keep from './provider'; const result: number = keep(1);",
    );
}

#[test]
fn direct_default_generic_arrow_imports_and_calls_keep_public_ids() {
    check_default_import(
        "export default <T>(value: T): T => value;",
        concat!(
            "import keep from './provider';\n",
            "const explicit: number = keep<number>(1);\n",
            "const inferred: 'kept' = keep('kept');\n",
        ),
    );
}

#[test]
fn default_generic_arrow_body_error_keeps_its_provider_location() {
    const PROVIDER: &str = "export default <T>(): string => 1;";
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/provider.ts", PROVIDER)
        .unwrap();
    filesystem
        .write_file(
            "/project/importer.ts",
            "import make from './provider'; const text: string = make<number>();",
        )
        .unwrap();
    let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["importer.ts".to_owned()],
        options(),
        |program, queries| {
            let calls = call_result_locations(program.source_file("/project/importer.ts").unwrap());
            let result_types = check_call_results(queries, &calls);
            assert_eq!(result_types.len(), 1);
            assert_eq!(queries.type_to_string(result_types[0].1).unwrap(), "string");
            queries.replay_sources().unwrap()
        },
    )
    .unwrap();
    assert_eq!(program.diagnostics(), replay.unwrap());
    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one provider diagnostic: {:?}",
            program.diagnostics()
        )
    };
    assert_eq!(
        diagnostic.file_name.as_deref(),
        Some("/project/provider.ts")
    );
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(
        diagnostic.message,
        "Type 'number' is not assignable to type 'string'."
    );
    let range = diagnostic.range.unwrap();
    assert_eq!(
        (range.start.get(), range.end.get()),
        span_within(PROVIDER, "=> 1", "1")
    );
}

#[derive(Clone, Copy)]
enum ImportedAnnotation {
    Shape,
    CellParameter,
    CellShape,
}

#[allow(clippy::too_many_lines)] // Keep imported annotations and their public replay in one callback.
fn check_imported_annotation(provider_text: &str, annotation: ImportedAnnotation) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/types.ts",
            "export interface Shape { id: number } export interface Cell<T> { value: T }",
        )
        .unwrap();
    filesystem
        .write_file("/project/provider.ts", provider_text)
        .unwrap();
    filesystem
        .write_file(
            "/project/importer.ts",
            "import keep from './provider'; const copy = keep;",
        )
        .unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["importer.ts".to_owned()],
        options(),
        |program, queries| {
            // This callback follows normal dependency-first Program checking.
            let provider = program.source_file("/project/provider.ts").unwrap();
            let importer = program.source_file("/project/importer.ts").unwrap();
            let types = program.source_file("/project/types.ts").unwrap();
            let arrow = arrow_nodes(provider);
            let shape = types
                .parse
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::InterfaceDeclaration(interface) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &types.parse.arena.get(interface.name)?.data
                    else {
                        return None;
                    };
                    (name.text == "Shape").then(|| types.node_ref(interface.name).unwrap())
                })
                .unwrap();
            let copy = importer
                .parse
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    Some(importer.node_ref(variable.name).unwrap())
                })
                .unwrap();
            let (clause, imported_name) = importer
                .parse
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ImportClause(clause) = &record.data else {
                        return None;
                    };
                    Some((
                        importer.node_ref(node).unwrap(),
                        importer.node_ref(clause.name?).unwrap(),
                    ))
                })
                .unwrap();
            let callable = queries.get_type_at_location(arrow.declaration).unwrap();
            assert_eq!(
                queries.get_symbol_at_location(arrow.declaration).unwrap(),
                None
            );
            assert_eq!(queries.get_type_at_location(copy).unwrap(), callable);
            assert_eq!(
                queries.get_type_at_location(imported_name).unwrap(),
                callable
            );
            let alias = queries
                .get_symbol_at_location(imported_name)
                .unwrap()
                .unwrap();
            assert_eq!(queries.get_symbol_declarations(alias).unwrap(), [clause]);
            let [(_, t_name)] = arrow.type_parameters.as_slice() else {
                panic!("expected one arrow type parameter")
            };
            let t = queries.get_type_at_location(*t_name).unwrap();
            let returned = queries
                .get_type_at_location(arrow.return_annotation)
                .unwrap();
            let shape_type = queries.get_type_at_location(shape).unwrap();
            assert_ne!(returned, t);
            assert_eq!(
                queries.get_type_at_location(arrow.parameters[0].0).unwrap(),
                returned
            );
            assert_eq!(
                queries.get_type_at_location(arrow.parameters[0].1).unwrap(),
                returned
            );
            assert_eq!(
                queries.get_type_at_location(arrow.body_expression).unwrap(),
                returned
            );
            assert_eq!(
                queries
                    .get_symbol_at_location(arrow.body_expression)
                    .unwrap(),
                queries
                    .get_symbol_at_location(arrow.parameters[0].0)
                    .unwrap()
            );
            let mut locations = vec![
                arrow.declaration,
                arrow.return_annotation,
                arrow.body_expression,
                *t_name,
                arrow.parameters[0].0,
                arrow.parameters[0].1,
                copy,
                imported_name,
                shape,
            ];
            match annotation {
                ImportedAnnotation::Shape => assert_eq!(returned, shape_type),
                ImportedAnnotation::CellParameter | ImportedAnnotation::CellShape => {
                    let NodeData::TypeReferenceNode(reference) = &provider
                        .parse
                        .arena
                        .get(arrow.return_annotation.node)
                        .unwrap()
                        .data
                    else {
                        panic!("expected the written Cell reference")
                    };
                    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice()
                    else {
                        panic!("expected the one written Cell argument")
                    };
                    let argument = provider.node_ref(*argument).unwrap();
                    let (expected, display) = match annotation {
                        ImportedAnnotation::CellParameter => (t, "Cell<T>"),
                        ImportedAnnotation::CellShape => (shape_type, "Cell<Shape>"),
                        ImportedAnnotation::Shape => unreachable!(),
                    };
                    assert_eq!(queries.get_type_at_location(argument).unwrap(), expected);
                    assert_eq!(queries.type_to_string(returned).unwrap(), display);
                    locations.push(argument);
                }
            }
            for (node, record) in provider.parse.arena.iter() {
                let NodeData::ImportSpecifier(specifier) = &record.data else {
                    continue;
                };
                let name = provider.node_ref(specifier.name).unwrap();
                let alias = queries.get_symbol_at_location(name).unwrap().unwrap();
                assert_eq!(
                    queries.get_symbol_declarations(alias).unwrap(),
                    [provider.node_ref(node).unwrap()]
                );
                locations.push(name);
            }
            let identities = locations
                .into_iter()
                .map(|node| {
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
        program.diagnostics()
    );
}

#[test]
fn default_generic_arrow_imported_shape_annotations_keep_public_ids() {
    check_imported_annotation(
        "import type { Shape } from './types'; export default <T>(value: Shape): Shape => value;",
        ImportedAnnotation::Shape,
    );
}

#[test]
fn default_generic_arrow_imported_cell_annotations_keep_the_arrow_parameter() {
    check_imported_annotation(
        "import type { Cell } from './types'; export default <T>(value: Cell<T>): Cell<T> => value;",
        ImportedAnnotation::CellParameter,
    );
}

#[test]
fn default_generic_arrow_nested_imported_shape_arguments_keep_public_ids() {
    check_imported_annotation(
        "import type { Cell, Shape } from './types'; export default <T>(value: Cell<Shape>): Cell<Shape> => value;",
        ImportedAnnotation::CellShape,
    );
}
