use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_checker::semantic::CanonicalModuleResolutionMode;
use ts_compiler::{
    CanonicalModuleResolutionLookup, CanonicalProgramQueries, Program, ProgramDiagnostic,
};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const MAIN: &str = "/project/main.ts";
const DECLARATIONS: &str = "/project/node_modules/@types/route-tools/index.d.ts";
const AMBIENT: &str = concat!(
    "declare module 'route-tools' {\n",
    "  namespace toolkit { interface Paths {\n",
    "    parent(input: string): string;\n",
    "    combine(...inputs: string[]): string;\n",
    "    ignored(input: boolean): boolean;\n",
    "    readonly alternate: Paths;\n",
    "  } }\n",
    "  const toolkit: toolkit.Paths; export = toolkit;\n",
    "}\n",
    "declare module 'portable:routes' {\n",
    "  import toolkit = require('route-tools'); export = toolkit;\n",
    "}\n",
);
const CONSUMER: &str = concat!(
    "import { parent as forwardedParent, combine as forwardedCombine } from 'portable:routes';\n",
    "import { parent as directParent, combine as directCombine } from 'route-tools';\n",
    "const parentValue = forwardedParent('part/file');\n",
    "const combinedValue = forwardedCombine('part', 'file');\n",
    "const emptyValue = forwardedCombine();\n",
    "const directValue = directParent('part/file');\n",
    "const directCombined = directCombine('part', 'file');\n",
    "const wrongArgument = forwardedParent(1);\n",
    "const wrongRest = forwardedCombine('part', 1);\n",
    "const wrongResult: number = forwardedParent('part/file');\n",
);

fn named_node(program: &Program, path: &str, kind: SyntaxKind, name: &str) -> NodeRef {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                NodeData::ModuleDeclaration(module) => module.name,
                _ => return None,
            };
            let text = match &source.parse.arena.get(name_node)?.data {
                NodeData::Identifier(identifier) => &identifier.text,
                NodeData::StringLiteral(literal) => &literal.text,
                _ => return None,
            };
            (text == name).then(|| source.node_ref(node).unwrap())
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name} in {path}"))
}

fn module_specifiers(program: &Program, path: &str) -> Vec<NodeRef> {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let specifier = match &record.data {
                NodeData::ImportDeclaration(import) => import.module_specifier,
                NodeData::ImportEqualsDeclaration(import) => {
                    let NodeData::ExternalModuleReference(reference) =
                        &source.parse.arena.get(import.module_reference)?.data
                    else {
                        return None;
                    };
                    reference.expression
                }
                _ => return None,
            };
            Some(source.node_ref(specifier).unwrap())
        })
        .collect()
}

fn call_callee(program: &Program, variable: &str) -> NodeRef {
    let source = program.source_file(MAIN).unwrap();
    let declaration = named_node(program, MAIN, SyntaxKind::VariableDeclaration, variable);
    let NodeData::VariableDeclaration(variable) =
        &source.parse.arena.get(declaration.node).unwrap().data
    else {
        panic!("the fixture variable must retain its declaration");
    };
    let NodeData::CallExpression(call) = &source
        .parse
        .arena
        .get(variable.initializer.unwrap())
        .unwrap()
        .data
    else {
        panic!("the fixture variable must retain its call initializer");
    };
    source.node_ref(call.expression).unwrap()
}

fn assert_ambient_target(
    program: &Program,
    queries: &CanonicalProgramQueries<'_>,
    specifier: NodeRef,
    name: &str,
    usage_mode: CanonicalModuleResolutionMode,
) {
    let CanonicalModuleResolutionLookup::Resolved(resolved) = queries.module_resolution(specifier)
    else {
        panic!("missing compiler resolution for {name}");
    };
    assert_eq!(
        resolved.target_file(),
        program.source_file(DECLARATIONS).unwrap().id
    );
    assert_eq!(resolved.usage_mode(), usage_mode);
    assert_eq!(
        resolved.target_mode(),
        CanonicalModuleResolutionMode::CommonJs
    );
    assert!(resolved.is_ambient_module());
    let declaration = named_node(program, DECLARATIONS, SyntaxKind::ModuleDeclaration, name);
    assert_eq!(
        queries
            .get_symbol_declarations(resolved.target_symbol())
            .unwrap(),
        &[declaration]
    );
}

fn assert_queries_and_replay(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
) -> Vec<ProgramDiagnostic> {
    let cold = queries.cold_diagnostic_snapshot();
    let imports = module_specifiers(program, MAIN);
    let require = module_specifiers(program, DECLARATIONS);
    assert_eq!(imports.len(), 2);
    assert_eq!(require.len(), 1);
    for (specifier, name, mode) in [
        (
            imports[0],
            "portable:routes",
            CanonicalModuleResolutionMode::Esm,
        ),
        (
            imports[1],
            "route-tools",
            CanonicalModuleResolutionMode::Esm,
        ),
        (
            require[0],
            "route-tools",
            CanonicalModuleResolutionMode::CommonJs,
        ),
    ] {
        assert_ambient_target(program, queries, specifier, name, mode);
    }
    let specifiers = [imports[0], imports[1], require[0]];
    let resolutions = specifiers.map(|node| queries.module_resolution(node));

    let mut methods = Vec::new();
    for (name, calls) in [
        ("parent", ["parentValue", "directValue"]),
        ("combine", ["combinedValue", "directCombined"]),
    ] {
        let declaration = named_node(program, DECLARATIONS, SyntaxKind::MethodSignature, name);
        let symbol = queries
            .get_symbol_at_location(declaration)
            .unwrap()
            .unwrap();
        assert_eq!(
            queries.get_symbol_declarations(symbol).unwrap(),
            &[declaration]
        );
        let type_ = queries.get_type_at_location(declaration).unwrap();
        for call in calls {
            assert_eq!(
                queries.get_type_at_location(call_callee(program, call)),
                Ok(type_)
            );
        }
        methods.push((declaration, symbol, type_));
    }
    for name in [
        "parentValue",
        "combinedValue",
        "emptyValue",
        "directValue",
        "directCombined",
        "wrongArgument",
        "wrongRest",
    ] {
        let declaration = named_node(program, MAIN, SyntaxKind::VariableDeclaration, name);
        let type_ = queries.get_type_at_location(declaration).unwrap();
        assert_eq!(queries.type_to_string(type_).unwrap(), "string");
    }

    assert_eq!(queries.replay_sources().unwrap(), cold);
    assert_eq!(
        specifiers.map(|node| queries.module_resolution(node)),
        resolutions
    );
    for (declaration, symbol, type_) in methods {
        assert_eq!(queries.get_type_at_location(declaration), Ok(type_));
        assert_eq!(
            queries.get_symbol_at_location(declaration),
            Ok(Some(symbol))
        );
        assert_eq!(
            queries.get_symbol_declarations(symbol).unwrap(),
            &[declaration]
        );
    }
    cold
}

#[test]
fn nodenext_esm_imports_ambient_methods_from_a_commonjs_declaration_package() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("/project/package.json", r#"{"type":"module"}"#),
        (
            "/project/node_modules/@types/route-tools/package.json",
            r#"{"name":"@types/route-tools","types":"index.d.ts"}"#,
        ),
        (DECLARATIONS, AMBIENT),
        (MAIN, CONSUMER),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::NodeNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::NodeNext,
            lib: Some(vec!["es5".to_owned()]),
            types: Some(vec!["route-tools".to_owned()]),
            strict: true,
            skip_lib_check: true,
            no_emit: true,
            ..CompilerOptions::default()
        },
        assert_queries_and_replay,
    )
    .unwrap();
    assert_eq!(
        program.diagnostics(),
        result.expect("the canonical checker ran")
    );
    assert_eq!(program.source_file(MAIN).unwrap().source_text, CONSUMER);
    assert_eq!(
        program.source_file(DECLARATIONS).unwrap().source_text,
        AMBIENT
    );
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2345), Some(2345), Some(2322)]
    );
    assert!(
        program
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.file_name.as_deref() == Some(MAIN))
    );
}
