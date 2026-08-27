use serde_json::{Value, json};
use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_compiler::{CanonicalProgramQueries, CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_parser::parse_source_file;
use ts_vfs::{FileSystem, MemoryFileSystem};

fn export_cache_state(text: &str) -> Value {
    let library = parse_source_file(include_str!("../../crates/ts_bundled/libs/lib.es5.d.ts"));
    let source = parse_source_file(text);
    assert!(library.diagnostics.is_empty() && source.diagnostics.is_empty());
    let library_file = FileId::new(147_000);
    let file = FileId::new(147_001);
    let mut binder = CanonicalBinder::new();
    for (id, parsed) in [(library_file, &library), (file, &source)] {
        let is_library = id == library_file;
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                id,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"/project/{}.ts\"", id.index())),
                    CanonicalSourceLanguage::TypeScript,
                    is_library,
                    is_library,
                    if is_library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for (id, parsed) in [(library_file, &library), (file, &source)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, id)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(library_file, &library.arena), (file, &source.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::EsNext,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let exported = source
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ExportAssignment(export) = &record.data else {
                return None;
            };
            Some(NodeRef::new(source.arena.id(), file, export.expression))
        })
        .unwrap();
    let declaration = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(
                record.kind,
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::EnumDeclaration
                    | SyntaxKind::FunctionDeclaration
            )
            .then_some(NodeRef::new(source.arena.id(), file, node))
        })
        .unwrap();
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let owner = context.store().get_merged_symbol(owner).unwrap();
    let cached_type = context
        .store()
        .type_node_links(exported)
        .and_then(|links| links.resolved_type);
    let cached_symbol = context
        .store()
        .symbol_node_links(exported)
        .and_then(|links| links.resolved_symbol);
    let bound_symbol = context.file(file).unwrap().1.symbol(exported);
    assert!(cached_type.is_none() && cached_symbol.is_none() && bound_symbol.is_none());
    let value = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let declared = context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type);
    let value_display = context
        .type_to_string(value)
        .map_err(|error| format!("{error:?}"));
    let declared_display = declared.map(|type_| {
        context
            .type_to_string(type_)
            .map_err(|error| format!("{error:?}"))
    });
    let actual = context.get_type_at_location(exported).unwrap();
    assert_eq!(actual, value);
    if matches!(
        source.arena.get(declaration.node).unwrap().kind,
        SyntaxKind::ClassDeclaration | SyntaxKind::EnumDeclaration
    ) {
        assert!(declared.is_some_and(|declared| declared != actual));
    }
    json!({
        "cachedTypeBefore": false, "cachedSymbolBefore": false, "boundSymbolBefore": false,
        "valueDisplayBefore": value_display, "declaredDisplayBefore": declared_display,
        "artifactUsesValueIdentity": actual == value,
    })
}

fn query(program: &Program, queries: &mut CanonicalProgramQueries<'_>, node: NodeRef) -> Value {
    let mut result = json!({});
    match queries.get_type_at_location(node) {
        Ok(type_) => {
            result["type"] = json!(
                queries
                    .type_to_string_at_location_with_flags(
                        type_,
                        node,
                        CanonicalTypeFormatFlags::NO_TRUNCATION
                    )
                    .map_err(|error| format!("{error:?}"))
            );
            result["typeId"] = json!(format!("{type_:?}"));
        }
        Err(error) => result["typeError"] = json!(format!("{error:?}")),
    }
    match queries.get_symbol_at_location(node) {
        Ok(Some(symbol)) => {
            result["symbol"] = json!(
                queries
                    .symbol_to_string_at_location(symbol, node)
                    .map_err(|error| format!("{error:?}"))
            );
            result["symbolId"] = json!(format!("{symbol:?}"));
            result["declarations"] = json!(
                queries
                    .get_symbol_declarations(symbol)
                    .unwrap()
                    .iter()
                    .map(|declaration| format!("{:?}", program.node(*declaration).unwrap().kind))
                    .collect::<Vec<_>>()
            );
        }
        Ok(None) => result["symbol"] = Value::Null,
        Err(error) => result["symbolError"] = json!(format!("{error:?}")),
    }
    result
}

fn main() {
    let path = std::env::var("TS_EXPORT_REVIEW_CASES").unwrap();
    let contents = std::fs::read_to_string(path).unwrap();
    let cases: Vec<Value> = serde_json::from_str(&contents).unwrap();
    let mut observations = Vec::new();
    for case in cases {
        let name = case["name"].as_str().unwrap();
        let main = case["main"].as_str().unwrap_or("input.ts");
        let export_file = case["exportFile"].as_str().unwrap_or(main);
        let filesystem = MemoryFileSystem::new(true);
        for (file, source) in case["files"].as_object().unwrap() {
            filesystem
                .write_file(&format!("/project/{file}"), source.as_str().unwrap())
                .unwrap();
        }
        let options = CompilerOptions {
            module: ModuleKind::NodeNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::NodeNext,
            target: ScriptTarget::EsNext,
            strict: true,
            strict_specified: true,
            no_emit: true,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        };
        let mut observation = json!({"name": name});
        if matches!(name, "class" | "enum" | "merged_callable") {
            observation["cacheState"] =
                export_cache_state(case["files"]["input.ts"].as_str().unwrap());
        }
        let result = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &[main.to_owned()],
            options,
            |program, queries| {
                let mut nodes = Vec::new();
                for file in [export_file, main] {
                    let source = program.source_file(&format!("/project/{file}")).unwrap();
                    for (node, record) in source.parse.arena.iter() {
                        match &record.data {
                            NodeData::ExportAssignment(export) if file == export_file => {
                                nodes.push(("export", source.node_ref(export.expression).unwrap()));
                            }
                            NodeData::VariableDeclaration(variable)
                                if matches!(&source.parse.arena.get(variable.name).unwrap().data,
                                    NodeData::Identifier(identifier) if identifier.text == "observed") =>
                            {
                                nodes.push((
                                    "read",
                                    source.node_ref(variable.initializer.unwrap()).unwrap(),
                                ));
                            }
                            NodeData::CallExpression(call) if file == main => {
                                nodes.push(("call", source.node_ref(node).unwrap()));
                                nodes.push(("callee", source.node_ref(call.expression).unwrap()));
                            }
                            _ => {}
                        }
                    }
                    if main == export_file {
                        break;
                    }
                }
                let before = queries.cold_diagnostic_snapshot();
                for (role, node) in &nodes {
                    observation[*role] = query(program, queries, *node);
                }
                match queries.replay_sources() {
                    Ok(diagnostics) => {
                        assert_eq!(diagnostics, before, "diagnostics changed for {name}");
                        for (role, node) in nodes {
                            assert_eq!(
                                query(program, queries, node),
                                observation[role],
                                "warm {name}/{role}"
                            );
                        }
                        observation["warmStable"] = json!(true);
                    }
                    Err(error) => observation["replayError"] = json!(format!("{error:?}")),
                }
                observation["diagnostics"] = json!(format!("{before:?}"));
            },
        );
        match result {
            Ok((program, callback)) => {
                observation["checked"] = json!(callback.is_some());
                observation["programDiagnostics"] = json!(format!("{:?}", program.diagnostics()));
            }
            Err(error) => observation["sourceError"] = json!(format!("{error:?}")),
        }
        observations.push(observation);
    }
    println!("{}", serde_json::to_string_pretty(&observations).unwrap());
}
