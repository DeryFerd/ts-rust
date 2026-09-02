use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError,
    IntrinsicBootstrapOptions, TypeData, TypeId, TypeNodeUnavailable,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(260_910);
const LIBRARIES: [(&str, &str); 3] = [
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

// These declarations retain the type expressions from Hono's src/router.ts.
const ROUTER_TYPES: &str = concat!(
    "export type ParamIndexMap = Record<string, number>\n",
    "export type ParamStash = string[]\n",
    "export type Params = Record<string, string>\n",
    "export type Result<T> = [[T, ParamIndexMap][], ParamStash] | [[T, Params][]]\n",
);

struct Fixture {
    source: ParseResult,
    libraries: [ParseResult; 3],
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parse = |source| {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            parsed
        };
        Self {
            source: parse(source),
            libraries: LIBRARIES.map(|(_, source)| parse(source)),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/lib/{}\"", LIBRARIES[index].0),
                    true,
                    CanonicalModuleState::Script,
                )
            })
            .collect::<Vec<_>>();
        files.push((
            FILE,
            &self.source,
            "\"/project/router-results.ts\"".to_owned(),
            false,
            CanonicalModuleState::External,
        ));
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library, module) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        *module,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                strict_function_types: true,
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn alias(&self, context: &CanonicalCheckerContext<'_>, expected: &str) -> Alias {
        let (declaration, rhs) = self
            .source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some((
                    NodeRef::new(self.source.arena.id(), FILE, node),
                    NodeRef::new(self.source.arena.id(), FILE, alias.type_),
                ))
            })
            .unwrap_or_else(|| panic!("missing alias {expected}"));
        let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
        Alias {
            symbol: context.store().get_merged_symbol(raw).unwrap(),
            declaration,
            rhs,
        }
    }
}

#[derive(Clone, Copy)]
struct Alias {
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    rhs: NodeRef,
}

fn demand_alias(context: &mut CanonicalCheckerContext<'_>, alias: Alias) -> TypeId {
    let type_ = context.get_declared_type_of_symbol(alias.symbol).unwrap();
    assert_eq!(context.get_type_from_type_node(alias.rhs), Ok(type_));
    assert_eq!(
        context
            .store()
            .type_alias_links(alias.symbol)
            .unwrap()
            .declared_type,
        Some(type_)
    );
    type_
}

fn tuple_elements<'a>(context: &'a CanonicalCheckerContext<'_>, type_: TypeId) -> &'a [TypeId] {
    let TypeData::TypeReference(reference) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected a tuple reference")
    };
    let target = reference.object.target.unwrap();
    assert!(matches!(
        context.store().type_payload(target).unwrap().data(),
        TypeData::Tuple(_)
    ));
    reference.resolved_type_arguments.as_deref().unwrap()
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId, target: TypeId) -> TypeId {
    let TypeData::TypeReference(reference) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected an array reference")
    };
    assert_eq!(reference.object.target, Some(target));
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("an array has one element type")
    };
    *element
}

fn assert_result(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    handler: TypeId,
    [index_map, stash, params]: [TypeId; 3],
    array: TypeId,
) {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("both router result formats must remain in the union")
    };
    assert_eq!(union.union.types.len(), 2);
    let mut lengths = Vec::new();
    for &branch in &union.union.types {
        let elements = tuple_elements(context, branch);
        let map = match elements {
            [_, actual_stash] => {
                assert_eq!(*actual_stash, stash);
                index_map
            }
            [_] => params,
            _ => panic!("the result has one or two tuple elements"),
        };
        let entry = array_element(context, elements[0], array);
        assert_eq!(tuple_elements(context, entry), &[handler, map]);
        lengths.push(elements.len());
    }
    lengths.sort_unstable();
    assert_eq!(lengths, [1, 2]);
}

#[test]
#[allow(clippy::too_many_lines)] // One graph checks the formal, instantiations, and replay.
fn router_tuple_union_preserves_handler_maps_and_stash() {
    let fixture = Fixture::new(&format!(
        "{ROUTER_TYPES}\
         type TextResult = Result<string>;\n\
         type NumberResult = Result<number>;\n\
         type Renamed<Item> = [[Item, ParamIndexMap][], ParamStash] | [[Item, Params][]];\n\
         type RenamedText = Renamed<string>;\n\
         type Forward<Handler = string> = Result<Handler>;\n\
         type DefaultResult = Forward;\n\
         type ForwardNumber = Forward<number>;\n"
    ));
    for query_first in [false, true] {
        let mut context = fixture.context();
        let aliases = [
            "Result",
            "TextResult",
            "NumberResult",
            "Renamed",
            "RenamedText",
            "Forward",
            "DefaultResult",
            "ForwardNumber",
        ]
        .map(|name| fixture.alias(&context, name));
        if query_first {
            context.get_type_from_type_node(aliases[0].rhs).unwrap();
        }
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let resolved = aliases.map(|alias| demand_alias(&mut context, alias));
        let dependencies = ["ParamIndexMap", "ParamStash", "Params"]
            .map(|name| fixture.alias(&context, name))
            .map(|alias| demand_alias(&mut context, alias));
        let [index_map, stash, params] = dependencies;
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        for (map, value) in [(index_map, number), (params, string)] {
            let TypeData::Mapped(mapped) = context.store().type_payload(map).unwrap().data()
            else {
                panic!("the parameter map must retain its Record instantiation")
            };
            assert_eq!(mapped.constraint_type, Some(string));
            assert_eq!(mapped.template_type, Some(value));
        }
        let TypeData::TypeReference(stash_reference) =
            context.store().type_payload(stash).unwrap().data()
        else {
            panic!("the parameter stash must remain a string array")
        };
        let array = stash_reference.object.target.unwrap();
        assert_eq!(array_element(&context, stash, array), string);
        let formals = [aliases[0], aliases[3], aliases[5]].map(|alias| {
            let links = context.store().type_alias_links(alias.symbol).unwrap();
            let [formal] = links.type_parameters.as_deref().unwrap() else {
                panic!("the alias has exactly one type parameter")
            };
            let NodeData::TypeAliasDeclaration(declaration) =
                &fixture.source.arena.get(alias.declaration.node).unwrap().data
            else {
                panic!("expected the source alias declaration")
            };
            let [parameter] = declaration.type_parameters.as_ref().unwrap().nodes.as_slice()
            else {
                panic!("the source alias has exactly one type parameter")
            };
            let parameter = NodeRef::new(fixture.source.arena.id(), FILE, *parameter);
            let raw = context.file(FILE).unwrap().1.symbol(parameter).unwrap();
            let owner = context.store().get_merged_symbol(raw).unwrap();
            assert_eq!(context.store().type_payload(*formal).unwrap().symbol(), Some(owner));
            assert!(matches!(
                context.store().type_payload(*formal).unwrap().data(),
                TypeData::TypeParameter(_)
            ));
            *formal
        });
        assert_ne!(formals[0], formals[1]);
        assert_ne!(formals[0], formals[2]);
        let TypeData::TypeParameter(forwarded) =
            context.store().type_payload(formals[2]).unwrap().data()
        else {
            panic!("the forwarded alias retains its own formal")
        };
        assert_eq!(forwarded.resolved_default_type, Some(string));
        for (type_, handler) in resolved
            .into_iter()
            .zip([formals[0], string, number, formals[1], string, formals[2], string, number])
        {
            assert_result(&context, type_, handler, dependencies, array);
        }
        assert_ne!(resolved[1], resolved[2]);
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().type_alias_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                aliases.map(|alias| context.store().type_node_links(alias.rhs).cloned()),
                aliases.map(|alias| context.store().type_alias_links(alias.symbol).cloned()),
                context.diagnostics().clone(),
            )
        };
        let warm = snapshot(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (alias, expected) in aliases.into_iter().zip(resolved) {
                assert_eq!(demand_alias(&mut context, alias), expected);
            }
            assert_eq!(snapshot(&context), warm, "query_first={query_first}");
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn router_tuple_union_reports_incompatible_handler_assignment() {
    let fixture = Fixture::new(&format!(
        "{ROUTER_TYPES}\
         declare const text: Result<string>;\n\
         const good: Result<string> = text;\n\
         const bad: Result<number> = text;\n"
    ));
    let mut context = fixture.context();
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the incompatible handler assignment must fail")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'Result<string>' is not assignable to type 'Result<number>'."
    );
    let (bad, bad_name) = fixture
        .source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &fixture.source.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "bad").then_some((
                NodeRef::new(fixture.source.arena.id(), FILE, node),
                NodeRef::new(fixture.source.arena.id(), FILE, variable.name),
            ))
        })
        .unwrap();
    assert_eq!(diagnostic.node, Some(bad_name));
    let raw = context.file(FILE).unwrap().1.symbol(bad).unwrap();
    let symbol = context.store().get_merged_symbol(raw).unwrap();
    let bad_type = context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(context.type_to_string(bad_type).unwrap(), "Result<number>");
    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context.store().value_symbol_links(symbol).unwrap().resolved_type,
        Some(bad_type)
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
    assert!(context.store().type_resolution_is_empty());
}

#[test]
fn tuple_union_dependency_walk_keeps_other_generic_alias_guards() {
    for body in ["[T]", "T[]", "number[] | [string]"] {
        let fixture = Fixture::new(&format!("export type Held<T> = {body};"));
        let mut context = fixture.context();
        let alias = fixture.alias(&context, "Held");
        let expected = DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::GenericReferenceUnsupported {
                node: alias.rhs,
                symbol: alias.symbol,
            },
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_type_from_type_node(alias.rhs),
                Err(expected.clone()),
                "{body}"
            );
            assert_eq!(
                context.get_declared_type_of_symbol(alias.symbol),
                Err(expected.clone()),
                "{body}"
            );
            assert!(context.diagnostics().is_empty());
            assert!(context.store().type_resolution_is_empty());
            assert!(context
                .store()
                .type_alias_links(alias.symbol)
                .and_then(|links| links.declared_type)
                .is_none());
        }
    }
}
