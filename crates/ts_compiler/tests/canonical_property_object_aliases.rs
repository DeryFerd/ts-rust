use ts_ast::{NodeData, SyntaxKind};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const FILE_NAME: &str = "/project/property-object-aliases.ts";

fn options() -> CompilerOptions {
    CompilerOptions {
        strict: true,
        no_emit: true,
        target: ScriptTarget::Es2025,
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The source check and artifact replay share one set of identities.
fn generic_object_alias_property_reads_keep_the_function_parameter_identity() {
    let text = "type Box<T>={value:T}; function read<T>(value:Box<T>):T{return value.value;}";
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, text).unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["property-object-aliases.ts".to_owned()],
        options(),
        |program, queries| {
            let source = program.source_file(FILE_NAME).unwrap();
            let (function_id, function) = source
                .parse
                .arena
                .iter()
                .find_map(|(id, record)| match &record.data {
                    NodeData::FunctionDeclaration(function) => Some((id, function)),
                    _ => None,
                })
                .unwrap();
            let parameter_id = function.type_parameters.as_ref().unwrap().nodes[0];
            let NodeData::TypeParameterDeclaration(parameter) =
                &source.parse.arena.get(parameter_id).unwrap().data
            else {
                panic!("read must retain its source type parameter");
            };
            let type_parameter_name = source.node_ref(parameter.name).unwrap();
            let type_parameter = queries.get_type_at_location(type_parameter_name).unwrap();
            let owner = queries
                .get_symbol_at_location(type_parameter_name)
                .unwrap()
                .unwrap();
            assert_eq!(
                queries.get_symbol_declarations(owner).unwrap(),
                [source.node_ref(parameter_id).unwrap()]
            );
            let returned = source.node_ref(function.type_.unwrap()).unwrap();
            assert_eq!(
                queries.get_type_at_location(returned).unwrap(),
                type_parameter
            );
            let property = source
                .parse
                .arena
                .iter()
                .find_map(|(id, record)| {
                    (record.kind == SyntaxKind::PropertyAccessExpression)
                        .then(|| source.node_ref(id).unwrap())
                })
                .unwrap();
            assert_eq!(
                queries.get_type_at_location(property).unwrap(),
                type_parameter
            );
            let alias_parameter = source
                .parse
                .arena
                .iter()
                .find_map(|(id, record)| match &record.data {
                    NodeData::TypeParameterDeclaration(parameter) if id != parameter_id => {
                        Some(source.node_ref(parameter.name).unwrap())
                    }
                    _ => None,
                })
                .unwrap();
            assert_ne!(
                queries.get_type_at_location(alias_parameter).unwrap(),
                type_parameter
            );
            let function_name = source.node_ref(function.name.unwrap()).unwrap();
            let callable = queries.get_type_at_location(function_name).unwrap();
            assert_eq!(
                queries
                    .get_type_at_location(source.node_ref(function_id).unwrap())
                    .unwrap(),
                callable
            );
            let cold = queries.cold_diagnostic_snapshot();
            assert!(cold.is_empty(), "{cold:?}");
            let store = queries.semantic_store_id();
            for _ in 0..2 {
                assert_eq!(queries.replay_sources().unwrap(), cold);
                assert_eq!(
                    queries.get_type_at_location(function_name).unwrap(),
                    callable
                );
                assert_eq!(
                    queries.get_type_at_location(property).unwrap(),
                    type_parameter
                );
                assert_eq!(
                    queries.get_type_at_location(returned).unwrap(),
                    type_parameter
                );
                assert_eq!(queries.semantic_store_id(), store);
            }
        },
    )
    .unwrap();
    result.expect("canonical checking and queries must run");
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(filesystem.read_file(FILE_NAME).unwrap(), text);
}

#[test]
fn distinct_object_alias_arguments_reject_the_wrong_assignment_on_replay() {
    let text = "type Box<T>={value:T}; declare const text:Box<string>; const bad:Box<number>=text;";
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(FILE_NAME, text).unwrap();
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["property-object-aliases.ts".to_owned()],
        options(),
        |_, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(cold.len(), 1, "{cold:?}");
            for _ in 0..2 {
                assert_eq!(queries.replay_sources().unwrap(), cold);
            }
        },
    )
    .unwrap();
    result.expect("canonical checking and queries must run");
    let [diagnostic] = program.diagnostics() else {
        panic!("the assignment must produce one diagnostic");
    };
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(diagnostic.file_name.as_deref(), Some(FILE_NAME));
    let range = diagnostic.range.unwrap();
    let start = u32::try_from(text.find("bad").unwrap()).unwrap();
    assert_eq!((range.start.get(), range.end.get()), (start, start + 3));
    assert_eq!(filesystem.read_file(FILE_NAME).unwrap(), text);
}
