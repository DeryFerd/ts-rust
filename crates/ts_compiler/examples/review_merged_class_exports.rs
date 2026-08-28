use std::{collections::BTreeMap, error::Error};

use serde::Deserialize;
use serde_json::{Value, json};
use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeFormatFlags,
    SourceCheckError, TypeData, TypeId,
};
use ts_diagnostics::Diagnostic;
use ts_options::ScriptTarget;
use ts_parser::parse_source_file;

#[derive(Clone, Deserialize)]
struct CaseFile {
    path: String,
    text: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Case {
    name: String,
    consumer: String,
    class_file: String,
    expect: String,
    files: Vec<CaseFile>,
}

type Sources = BTreeMap<FileId, CaseFile>;

fn error_value(error: impl std::fmt::Debug) -> Value {
    json!({"error": format!("{error:?}")})
}

fn node_value(context: &CanonicalCheckerContext<'_>, sources: &Sources, node: NodeRef) -> Value {
    let source = &sources[&node.file];
    let record = context.file(node.file).unwrap().0.get(node.node).unwrap();
    let start = record.range.start.get();
    let end = record.range.end.get();
    json!({
        "file": source.path, "kind": format!("{:?}", record.kind),
        "start": start, "end": end, "text": &source.text[start as usize..end as usize],
    })
}

fn symbol_value(
    context: &CanonicalCheckerContext<'_>,
    sources: &Sources,
    symbol: SemanticSymbolId,
) -> Value {
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    let record = context.store().symbol(symbol).unwrap();
    json!({
        "name": context.symbol_to_string(symbol).map_or_else(error_value, |name| json!(name)),
        "flags": record.flags().without(SymbolFlags::TRANSIENT).bits(),
        "transient": record.flags().contains(SymbolFlags::TRANSIENT),
        "declarations": record.declarations().unwrap_or_default().iter()
            .map(|node| node_value(context, sources, *node)).collect::<Vec<_>>(),
        "valueDeclaration": record.value_declaration().map(|node| node_value(context, sources, node)),
    })
}

fn diagnostic_value(
    context: &CanonicalCheckerContext<'_>,
    sources: &Sources,
    node: Option<NodeRef>,
    range: Option<ts_core::TextRange>,
    diagnostic: &Diagnostic,
    related: Vec<Value>,
) -> Value {
    let range = range.or_else(|| {
        node.map(|node| {
            context
                .file(node.file)
                .unwrap()
                .0
                .get(node.node)
                .unwrap()
                .range
        })
    });
    json!({
        "file": node.map(|node| &sources[&node.file].path),
        "start": range.map_or(-1, |range| i64::from(range.start.get())),
        "end": range.map_or(-1, |range| i64::from(range.end.get())),
        "code": diagnostic.code(), "category": diagnostic.category() as u8,
        "message": diagnostic.render().unwrap(), "related": related,
        "unnecessary": diagnostic.message.reports_unnecessary(),
        "deprecated": diagnostic.message.reports_deprecated(),
    })
}

fn diagnostics(context: &CanonicalCheckerContext<'_>, sources: &Sources) -> Vec<Value> {
    let mut result = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|record| {
            let related = record
                .related_information
                .iter()
                .map(|related| {
                    diagnostic_value(
                        context,
                        sources,
                        related.node,
                        None,
                        &related.diagnostic,
                        vec![],
                    )
                })
                .collect();
            diagnostic_value(
                context,
                sources,
                record.node,
                record.range_override.map(|range| range.range()),
                &record.diagnostic,
                related,
            )
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|diagnostic| {
        (
            diagnostic["file"].as_str().unwrap_or_default().to_owned(),
            diagnostic["start"].as_i64(),
            diagnostic["end"].as_i64(),
            diagnostic["code"].as_u64(),
            diagnostic["message"]
                .as_str()
                .unwrap_or_default()
                .to_owned(),
        )
    });
    result.dedup();
    result
}

fn type_role(type_: TypeId, declared: TypeId, value: TypeId) -> &'static str {
    if type_ == declared {
        "declared"
    } else if type_ == value {
        "value"
    } else {
        "other"
    }
}

fn display(context: &mut CanonicalCheckerContext<'_>, type_: TypeId, node: NodeRef) -> Value {
    context
        .type_to_string_at_location_with_flags(type_, node, CanonicalTypeFormatFlags::NO_TRUNCATION)
        .map_or_else(error_value, |text| json!(text))
}

fn query(
    context: &mut CanonicalCheckerContext<'_>,
    sources: &Sources,
    node: NodeRef,
    owner: SemanticSymbolId,
    declared: TypeId,
    value: TypeId,
) -> Value {
    let mut result = json!({});
    match context.get_type_at_location(node) {
        Ok(type_) => {
            result["type"] = display(context, type_, node);
            result["typeRole"] = json!(type_role(type_, declared, value));
        }
        Err(error) => result["typeError"] = json!(format!("{error:?}")),
    }
    match context.get_symbol_at_location(node) {
        Ok(symbol) => {
            let symbol = symbol.and_then(|symbol| context.store().get_merged_symbol(symbol));
            result["symbol"] =
                symbol.map_or(Value::Null, |symbol| symbol_value(context, sources, symbol));
            result["symbolIsOwner"] = json!(symbol == Some(owner));
        }
        Err(error) => result["symbolError"] = json!(format!("{error:?}")),
    }
    result
}

fn declaration_name(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<NodeRef> {
    let record = context.file(node.file)?.0.get(node.node)?;
    let name = match &record.data {
        NodeData::PropertyDeclaration(property) => property.name,
        NodeData::VariableDeclaration(variable) => variable.name,
        _ => return None,
    };
    Some(NodeRef::new(node.arena, node.file, name))
}

fn property_symbols(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<SemanticSymbolId> {
    let record = context.store().type_payload(type_).unwrap();
    let structured = match record.data() {
        TypeData::Interface(instance) => &instance.reference.object.structured,
        TypeData::Object(value) => &value.structured,
        _ => panic!("class identity has an unexpected type record"),
    };
    let mut properties = structured.properties.clone().unwrap_or_default();
    properties.sort_by_key(|symbol| context.store().symbol(*symbol).unwrap().name().to_owned());
    properties
}

fn members(
    context: &mut CanonicalCheckerContext<'_>,
    sources: &Sources,
    type_: TypeId,
    owner: SemanticSymbolId,
    enclosing: NodeRef,
) -> Vec<Value> {
    property_symbols(context, type_)
        .into_iter()
        .map(|symbol| {
            let record = context.store().symbol(symbol).unwrap();
            let name = record.name().as_utf8().unwrap().to_owned();
            let declaration = record.declarations().and_then(|nodes| nodes.first()).copied();
            let parent_is_owner = context.store().get_parent_of_symbol(symbol) == Some(owner);
            let member_type = context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type);
            let declaration_symbol_matches = declaration
                .and_then(|declaration| declaration_name(context, declaration))
                .map(|name| {
                    context.get_symbol_at_location(name).map_or_else(error_value, |resolved| {
                        json!(resolved.and_then(|symbol| context.store().get_merged_symbol(symbol))
                            == context.store().get_merged_symbol(symbol))
                    })
                });
            let type_display = if name == "prototype" {
                Value::Null
            } else {
                member_type.map_or_else(
                    || json!({"error": "member value type is not published"}),
                    |type_| display(context, type_, enclosing),
                )
            };
            json!({
                "name": name, "type": type_display, "symbol": symbol_value(context, sources, symbol),
                "parentIsOwner": parent_is_owner,
                "declarationSymbolMatches": declaration_symbol_matches,
            })
        })
        .collect()
}

struct QuerySites {
    nodes: BTreeMap<String, NodeRef>,
    reads: Vec<String>,
    namespaces: Vec<String>,
    owner: SemanticSymbolId,
    alias: SemanticSymbolId,
    consumer: FileId,
}

fn snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    sources: &Sources,
    sites: &QuerySites,
) -> Value {
    let Some(declared) = context
        .store()
        .declared_type_links(sites.owner)
        .and_then(|links| links.declared_type)
    else {
        return json!({"error": "source checking did not publish the class declared identity"});
    };
    let Some(value) = context
        .store()
        .value_symbol_links(sites.owner)
        .and_then(|links| links.resolved_type)
    else {
        return json!({"error": "source checking did not publish the class value identity"});
    };
    let queries = sites
        .nodes
        .iter()
        .map(|(role, node)| {
            (
                role.clone(),
                query(context, sources, *node, sites.owner, declared, value),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let exported = sites.nodes["export"];
    let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
        return json!({"error": "class value is not an object"});
    };
    let constructors = object.structured.signatures.as_deref().unwrap_or_default()
        .iter().skip(object.structured.call_signature_count)
        .map(|signature| {
            let signature = context.store().signature(*signature).unwrap();
            json!({"parameters": signature.parameters().len(), "returnsDeclared": signature.resolved_return_type() == Some(declared)})
        }).collect::<Vec<_>>();
    let alias = context
        .resolve_alias(sites.alias)
        .map_or_else(error_value, |resolved| {
            json!(resolved.target == AliasTargetState::Resolved(sites.owner))
        });
    json!({
        "diagnostics": diagnostics(context, sources), "owner": symbol_value(context, sources, sites.owner),
        "queries": queries, "constructors": constructors, "aliasTargetIsOwner": alias,
        "types": {"declared": display(context, declared, exported), "value": display(context, value, exported), "distinct": declared != value},
        "instanceMembers": members(context, sources, declared, sites.owner, exported),
        "valueMembers": members(context, sources, value, sites.owner, exported),
    })
}

fn cache_state(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> Value {
    json!({
        "declared": context.store().declared_type_links(owner).and_then(|links| links.declared_type).is_some(),
        "value": context.store().value_symbol_links(owner).and_then(|links| links.resolved_type).is_some(),
    })
}

enum FirstQuery {
    Type(Result<TypeId, String>),
    Symbol(Result<Option<SemanticSymbolId>, String>),
}

fn observe(row: &Case, order: &str) -> Value {
    let mut result = json!({"name": row.name, "order": order, "expect": row.expect});
    let inputs = std::iter::once(CaseFile {
        path: "lib.es5.d.ts".to_owned(),
        text: include_str!("../../ts_bundled/libs/lib.es5.d.ts").to_owned(),
    })
    .chain(row.files.iter().cloned())
    .collect::<Vec<_>>();
    let parsed = inputs
        .iter()
        .map(|file| parse_source_file(&file.text))
        .collect::<Vec<_>>();
    let files = (0..inputs.len())
        .map(|index| FileId::new(152_000 + u32::try_from(index).unwrap()))
        .collect::<Vec<_>>();
    let sources: Sources = files.iter().copied().zip(inputs.iter().cloned()).collect();
    let mut binder = CanonicalBinder::new();
    for (index, ((input, source), file)) in inputs.iter().zip(&parsed).zip(&files).enumerate() {
        if !source.diagnostics.is_empty() {
            result["sourceStatus"] = json!("parse_error");
            result["sourceError"] = json!(format!("{:?}", source.diagnostics));
            return result;
        }
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                *file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"/project/{}\"", input.path)),
                    CanonicalSourceLanguage::TypeScript,
                    input.path.ends_with(".d.ts"),
                    index == 0,
                    if input.path == row.consumer {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for (source, file) in parsed.iter().zip(&files) {
        binder
            .bind_typescript_declaration_slice(&source.arena, *file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        parsed
            .iter()
            .zip(&files)
            .map(|(source, file)| (*file, &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::EsNext,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    let mut nodes = BTreeMap::new();
    let mut reads = Vec::new();
    let mut namespaces = Vec::new();
    let mut owner = None;
    let mut alias = None;
    let mut consumer = None;
    for ((input, source), file) in inputs.iter().zip(&parsed).zip(&files).skip(1) {
        let bound = context.file(*file).unwrap().1;
        if !bound.diagnostics().is_empty() {
            result["sourceStatus"] = json!("bind_error");
            result["sourceError"] = json!(format!("{:?}", bound.diagnostics()));
            return result;
        }
        let reference = |node| NodeRef::new(source.arena.id(), *file, node);
        let mut namespace_index = 0;
        for (id, record) in source.arena.iter() {
            match &record.data {
                NodeData::ClassDeclaration(class) if input.path == row.class_file => {
                    if let Some(name) = class.name
                        && matches!(&source.arena.get(name).unwrap().data, NodeData::Identifier(name) if name.text == "Value")
                    {
                        nodes.insert("class".to_owned(), reference(name));
                        owner = bound
                            .symbol(reference(id))
                            .and_then(|owner| context.store().get_merged_symbol(owner));
                    }
                }
                NodeData::ModuleDeclaration(module) if matches!(&source.arena.get(module.name).unwrap().data, NodeData::Identifier(name) if name.text == "Value") =>
                {
                    let role = format!("namespace:{}:{namespace_index}", input.path);
                    namespace_index += 1;
                    nodes.insert(role.clone(), reference(module.name));
                    namespaces.push(role);
                }
                NodeData::ExportAssignment(export) if input.path == row.consumer => {
                    nodes.insert("export".to_owned(), reference(export.expression));
                    alias = bound.symbol(reference(id));
                    consumer = Some(*file);
                }
                NodeData::VariableDeclaration(variable) if input.path == row.consumer => {
                    if let Some(initializer) = variable.initializer
                        && matches!(&source.arena.get(initializer).unwrap().data, NodeData::Identifier(name) if name.text == "Value")
                        && let NodeData::Identifier(name) =
                            &source.arena.get(variable.name).unwrap().data
                    {
                        let role = format!("read:{}", name.text);
                        nodes.insert(role.clone(), reference(initializer));
                        reads.push(role);
                    }
                }
                _ => {}
            }
        }
    }
    let sites = QuerySites {
        nodes,
        reads,
        namespaces,
        owner: owner.unwrap(),
        alias: alias.unwrap(),
        consumer: consumer.unwrap(),
    };
    if order == "read-first" && sites.reads.is_empty()
        || order == "namespace-first" && sites.namespaces.is_empty()
    {
        result["skippedOrder"] = json!(true);
        return result;
    }
    let (role, kind) = match order {
        "read-first" => (sites.reads[0].as_str(), "type"),
        "class-first" => ("class", "type"),
        "namespace-first" => (sites.namespaces[0].as_str(), "type"),
        "symbol-first" => ("export", "symbol"),
        "alias-first" => ("export", "alias"),
        _ => ("export", "type"),
    };
    let before_first = cache_state(&context, sites.owner);
    let first = match kind {
        "symbol" => FirstQuery::Symbol(
            context
                .get_symbol_at_location(sites.nodes[role])
                .map_err(|error| format!("{error:?}")),
        ),
        "alias" => FirstQuery::Symbol(
            context
                .resolve_alias(sites.alias)
                .map(|resolved| match resolved.target {
                    AliasTargetState::Resolved(symbol) => Some(symbol),
                    _ => None,
                })
                .map_err(|error| format!("{error:?}")),
        ),
        _ => FirstQuery::Type(
            context
                .get_type_at_location(sites.nodes[role])
                .map_err(|error| format!("{error:?}")),
        ),
    };
    let after_first = cache_state(&context, sites.owner);
    let checked = context.check_source_file(sites.consumer);
    result["cacheHistory"] = json!({"beforeFirst": before_first, "afterFirst": after_first, "afterSource": cache_state(&context, sites.owner)});
    let mut first_value = json!({"role": role, "kind": kind});
    let declared = context
        .store()
        .declared_type_links(sites.owner)
        .and_then(|links| links.declared_type);
    let value = context
        .store()
        .value_symbol_links(sites.owner)
        .and_then(|links| links.resolved_type);
    match first {
        FirstQuery::Type(Ok(type_)) => {
            first_value["type"] = display(&mut context, type_, sites.nodes[role]);
            if let (Some(declared), Some(value)) = (declared, value) {
                first_value["typeRole"] = json!(type_role(type_, declared, value));
            }
            first_value["stable"] =
                json!(context.get_type_at_location(sites.nodes[role]) == Ok(type_));
        }
        FirstQuery::Symbol(Ok(symbol)) => {
            first_value["symbol"] = symbol.map_or(Value::Null, |symbol| {
                symbol_value(&context, &sources, symbol)
            });
            first_value["symbolIsOwner"] = json!(
                symbol.and_then(|symbol| context.store().get_merged_symbol(symbol))
                    == Some(sites.owner)
            );
            let repeated = if kind == "alias" {
                context
                    .resolve_alias(sites.alias)
                    .ok()
                    .and_then(|resolved| match resolved.target {
                        AliasTargetState::Resolved(symbol) => Some(symbol),
                        _ => None,
                    })
            } else {
                context
                    .get_symbol_at_location(sites.nodes[role])
                    .ok()
                    .flatten()
            };
            first_value["stable"] = json!(repeated == symbol);
        }
        FirstQuery::Type(Err(error)) | FirstQuery::Symbol(Err(error)) => {
            first_value["error"] = json!(error)
        }
    }
    result["first"] = first_value;
    if let Err(error) = checked {
        result["sourceStatus"] = json!(if matches!(error, SourceCheckError::Unsupported(_)) {
            "unsupported"
        } else {
            "error"
        });
        result["sourceError"] = json!(format!("{error:?}"));
        result["diagnostics"] = json!(diagnostics(&context, &sources));
        return result;
    }
    result["sourceStatus"] = json!("checked");
    let before = snapshot(&mut context, &sources, &sites);
    let ids = sites
        .nodes
        .iter()
        .map(|(role, node)| {
            (
                role.clone(),
                context.get_type_at_location(*node),
                context.get_symbol_at_location(*node),
            )
        })
        .collect::<Vec<_>>();
    let mut stable = true;
    for _ in 0..2 {
        if let Err(error) = context.recheck_source_file(sites.consumer) {
            result["replayError"] = json!(format!("{error:?}"));
            stable = false;
            break;
        }
        for (role, type_, symbol) in &ids {
            stable &= context.get_type_at_location(sites.nodes[role]) == *type_;
            stable &= context.get_symbol_at_location(sites.nodes[role]) == *symbol;
        }
        stable &= snapshot(&mut context, &sources, &sites) == before;
    }
    result["snapshot"] = before;
    result["warmStable"] = json!(stable);
    result
}

fn main() -> Result<(), Box<dyn Error>> {
    let cases: Vec<Case> = serde_json::from_str(include_str!(
        "../../../docs/probes/merged_class_export_cases.json"
    ))?;
    let mut observations = Vec::new();
    let mut failures = Vec::new();
    for row in &cases {
        for order in [
            "export-first",
            "read-first",
            "symbol-first",
            "class-first",
            "namespace-first",
            "alias-first",
        ] {
            let observation =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| observe(row, order)))
                    .unwrap_or_else(|failure| {
                        let message = failure
                            .downcast_ref::<String>()
                            .map(String::as_str)
                            .or_else(|| failure.downcast_ref::<&str>().copied())
                            .unwrap_or("non-string panic");
                        json!({"name": row.name, "order": order, "expect": row.expect,
                    "sourceStatus": "observer_panic", "sourceError": message})
                    });
            if observation["skippedOrder"] != true {
                if observation["sourceStatus"] == "observer_panic" {
                    failures.push(format!("{}/{order}: observer panicked", row.name));
                }
                if row.expect == "required" && observation["sourceStatus"] != "checked" {
                    failures.push(format!(
                        "{}/{order}: original supported source failed",
                        row.name
                    ));
                }
                if row.expect == "boundary" && observation["sourceStatus"] == "checked" {
                    failures.push(format!(
                        "{}/{order}: original unsupported source was admitted",
                        row.name
                    ));
                }
                if observation
                    .get("warmStable")
                    .is_some_and(|stable| stable != true)
                {
                    failures.push(format!(
                        "{}/{order}: forced replay changed a result",
                        row.name
                    ));
                }
            }
            observations.push(observation);
        }
    }
    let output = serde_json::to_string_pretty(&observations)?;
    if let Ok(path) = std::env::var("TS_MERGED_EXPORT_RUST_REPORT") {
        std::fs::write(path, &output)?;
    } else {
        println!("{output}");
    }
    eprintln!("Collected {} Rust case/order rows", observations.len());
    if !failures.is_empty() {
        return Err(failures.join("\n").into());
    }
    Ok(())
}
