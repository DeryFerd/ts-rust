use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const HELPER_FILE: FileId = FileId::new(1_000);
const SOURCE_FILE: FileId = FileId::new(1_001);

macro_rules! bundled_libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((
            concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")),
        )),+]
    };
}

// The full lib.esnext.full.d.ts closure, in the bundled library priority order.
const LIBRARIES: &[(&str, &str)] = bundled_libraries!(
    "es5",
    "es2015",
    "es2016",
    "es2017",
    "es2018",
    "es2019",
    "es2020",
    "es2021",
    "es2022",
    "es2023",
    "es2024",
    "es2025",
    "esnext",
    "dom",
    "dom.iterable",
    "dom.asynciterable",
    "webworker.importscripts",
    "scripthost",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "es2016.array.include",
    "es2016.intl",
    "es2017.arraybuffer",
    "es2017.date",
    "es2017.object",
    "es2017.sharedmemory",
    "es2017.string",
    "es2017.intl",
    "es2017.typedarrays",
    "es2018.asyncgenerator",
    "es2018.asynciterable",
    "es2018.intl",
    "es2018.promise",
    "es2018.regexp",
    "es2019.array",
    "es2019.object",
    "es2019.string",
    "es2019.symbol",
    "es2019.intl",
    "es2020.bigint",
    "es2020.date",
    "es2020.promise",
    "es2020.sharedmemory",
    "es2020.string",
    "es2020.symbol.wellknown",
    "es2020.intl",
    "es2020.number",
    "es2021.promise",
    "es2021.string",
    "es2021.weakref",
    "es2021.intl",
    "es2022.array",
    "es2022.error",
    "es2022.intl",
    "es2022.object",
    "es2022.string",
    "es2022.regexp",
    "es2023.array",
    "es2023.collection",
    "es2023.intl",
    "es2024.arraybuffer",
    "es2024.collection",
    "es2024.object",
    "es2024.promise",
    "es2024.regexp",
    "es2024.sharedmemory",
    "es2024.string",
    "es2025.collection",
    "es2025.float16",
    "es2025.intl",
    "es2025.iterator",
    "es2025.promise",
    "es2025.regexp",
    "esnext.array",
    "esnext.collection",
    "esnext.date",
    "esnext.decorators",
    "esnext.disposable",
    "esnext.error",
    "esnext.intl",
    "esnext.sharedmemory",
    "esnext.temporal",
    "esnext.typedarrays",
    "decorators",
    "decorators.legacy",
    "esnext.full",
);

// Exact original Pathe helper, including its final LF.
const INTERNAL: &str = r#"// Util to normalize windows paths to posix
export function normalizeWindowsPath(input = "") {
  if (!input) {
    return input;
  }

  let normalized = input;
  if (normalized.includes("\\")) {
    normalized = normalized.replace(/\\/g, "/");
  }

  const driveLetter = normalized[0];
  if (
    driveLetter &&
    normalized[1] === ":" &&
    normalized[2] === "/" &&
    driveLetter >= "a" &&
    driveLetter <= "z"
  ) {
    normalized = driveLetter.toUpperCase() + normalized.slice(1);
  }

  return normalized;
}
"#;

const SOURCE: &str = r#"import { normalizeWindowsPath } from "../src/_internal";
export const cases = {
  [normalizeWindowsPath(String.raw`C:\temp\..`)]: "C:",
  [normalizeWindowsPath("C:\\a\\..\\")]: "C:",
};
declare const lookup: string;
export const value = cases[lookup];
"#;

struct Fixture {
    helper: ParseResult,
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parse = |name: &str, text: &str| {
            let parsed = parse_source_file(text);
            assert!(
                parsed.diagnostics.is_empty(),
                "{name}: {:?}",
                parsed.diagnostics
            );
            parsed
        };
        Self {
            helper: parse("/src/_internal.ts", INTERNAL),
            source: parse("/test/string_raw_key.ts", source),
            libraries: LIBRARIES
                .iter()
                .map(|(name, text)| parse(name, text))
                .collect(),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let options = CompilerOptions {
            target: ScriptTarget::EsNext,
            module: ModuleKind::EsNext,
            module_specified: true,
            strict: true,
            strict_specified: true,
            always_strict: true,
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_null_checks: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_unchecked_indexed_access: true,
            no_unused_locals: true,
            no_implicit_override: true,
            skip_lib_check: true,
            es_module_interop: true,
            force_consistent_casing_in_file_names: true,
            isolated_modules: true,
            no_emit: true,
            verbatim_module_syntax: true,
            ..CompilerOptions::default()
        };
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([
                (
                    HELPER_FILE,
                    &self.helper,
                    "\"/src/_internal.ts\"".to_owned(),
                    false,
                ),
                (
                    SOURCE_FILE,
                    &self.source,
                    "\"/test/string_raw_key.ts\"".to_owned(),
                    false,
                ),
            ])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
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
                        if *library {
                            CanonicalModuleState::Script
                        } else {
                            CanonicalModuleState::External
                        },
                    )
                    .with_implied_node_format(ModuleKind::EsNext),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        let imports = self
            .source
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => {
                    Some(node(&self.source, SOURCE_FILE, import.module_specifier))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let [specifier] = imports.as_slice() else {
            panic!("the consumer must retain its one real helper import")
        };
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: options.strict_null_checks,
                    exact_optional_property_types: options.exact_optional_property_types,
                },
                strict_bind_call_apply: options.strict_bind_call_apply,
                strict_builtin_iterator_return: options.strict_builtin_iterator_return,
                strict_function_types: options.strict_function_types,
                strict_property_initialization: options.strict_property_initialization,
                use_unknown_in_catch_variables: options.use_unknown_in_catch_variables,
                no_implicit_any: options.no_implicit_any,
                no_implicit_this: options.no_implicit_this,
                no_unchecked_indexed_access: options.no_unchecked_indexed_access,
                no_unused_locals: options.no_unused_locals,
                isolated_modules: options.isolated_modules,
                module_kind: options.module,
                no_emit: options.no_emit,
                check_bigint_target: true,
                name_resolution: (&options).into(),
                ..CanonicalCheckerOptions::default()
            },
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    *specifier,
                    CanonicalResolvedModuleInput::new(
                        HELPER_FILE,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
            ]),
        )
        .unwrap()
    }

    fn library(&self, name: &str) -> (FileId, &ParseResult) {
        let index = LIBRARIES
            .iter()
            .position(|(entry, _)| *entry == name)
            .unwrap();
        (
            FileId::new(u32::try_from(index).unwrap()),
            &self.libraries[index],
        )
    }

    fn library_declaration(&self, library: &str, kind: SyntaxKind, name: &str) -> NodeRef {
        let (file, parsed) = self.library(library);
        named_declaration(parsed, file, kind, name)
    }

    fn variable(&self, name: &str) -> (NodeRef, NodeRef) {
        let declaration = named_declaration(
            &self.source,
            SOURCE_FILE,
            SyntaxKind::VariableDeclaration,
            name,
        );
        let NodeData::VariableDeclaration(variable) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        (
            node(&self.source, SOURCE_FILE, variable.name),
            node(&self.source, SOURCE_FILE, variable.initializer.unwrap()),
        )
    }

    fn tracked_nodes(&self) -> Vec<NodeRef> {
        let mut nodes = [(HELPER_FILE, &self.helper), (SOURCE_FILE, &self.source)]
            .into_iter()
            .flat_map(|(file, parsed)| {
                parsed
                    .arena
                    .iter()
                    .map(move |(id, _)| node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        for (library, kind, name) in [
            ("lib.es5.d.ts", SyntaxKind::VariableDeclaration, "String"),
            (
                "lib.es5.d.ts",
                SyntaxKind::InterfaceDeclaration,
                "TemplateStringsArray",
            ),
            (
                "lib.es2015.core.d.ts",
                SyntaxKind::InterfaceDeclaration,
                "StringConstructor",
            ),
            ("lib.es2015.core.d.ts", SyntaxKind::MethodSignature, "raw"),
        ] {
            nodes.push(self.library_declaration(library, kind, name));
        }
        nodes
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named_declaration(
    parsed: &ParseResult,
    file: FileId,
    kind: SyntaxKind,
    expected: &str,
) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::FunctionDeclaration(function) => function.name?,
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = matches.as_slice() else {
        panic!("expected one {kind:?} named {expected}, got {matches:?}")
    };
    *declaration
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    computed: NodeRef,
    call: NodeRef,
    argument: NodeRef,
}

fn properties(fixture: &Fixture, object: NodeRef) -> [Property; 2] {
    let parsed = &fixture.source;
    let NodeData::ObjectLiteralExpression(object) = &parsed.arena.get(object.node).unwrap().data
    else {
        panic!("expected the original object literal")
    };
    object
        .properties
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::PropertyAssignment(property) = &parsed.arena.get(id).unwrap().data else {
                panic!("expected a property assignment")
            };
            let NodeData::ComputedPropertyName(computed) =
                &parsed.arena.get(property.name).unwrap().data
            else {
                panic!("expected the actual computed name")
            };
            let NodeData::CallExpression(call) =
                &parsed.arena.get(computed.expression).unwrap().data
            else {
                panic!("each computed key must retain the imported call")
            };
            let [argument] = call.arguments.nodes.as_slice() else {
                panic!("each imported call must retain one argument")
            };
            Property {
                declaration: node(parsed, SOURCE_FILE, id),
                computed: node(parsed, SOURCE_FILE, property.name),
                call: node(parsed, SOURCE_FILE, computed.expression),
                argument: node(parsed, SOURCE_FILE, *argument),
            }
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|_| panic!("expected the two original computed keys"))
}

fn resolved(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing type for {location:?}"))
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(location.file)
        .unwrap()
        .1
        .symbol(location)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn assert_signature(
    context: &CanonicalCheckerContext<'_>,
    call: NodeRef,
    declaration: NodeRef,
    parameters: &[NodeRef],
    minimum: i32,
    result: TypeId,
) -> SignatureId {
    let signature = context
        .store()
        .signature_links(call)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| panic!("missing selected signature for {call:?}"));
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.resolved_return_type(), Some(result));
    assert_eq!(record.min_argument_count(), minimum);
    assert_eq!(record.parameters().len(), parameters.len());
    for (&symbol, &parameter) in record.parameters().iter().zip(parameters) {
        let record = context.store().symbol(symbol).unwrap();
        assert_eq!(record.declarations(), Some(&[parameter][..]));
        assert_eq!(record.value_declaration(), Some(parameter));
        assert_eq!(symbol, bound_symbol(context, parameter));
    }
    signature
}

fn assert_types(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    object: NodeRef,
    properties: &[Property; 2],
) -> TypeId {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (string, undefined) = (bootstrap.string_type, bootstrap.undefined_type);
    let helper = named_declaration(
        &fixture.helper,
        HELPER_FILE,
        SyntaxKind::FunctionDeclaration,
        "normalizeWindowsPath",
    );
    let NodeData::FunctionDeclaration(function) =
        &fixture.helper.arena.get(helper.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(function.body.is_some());
    assert!(
        function.type_.is_none(),
        "the helper return must remain inferred"
    );
    let helper_parameters = function
        .parameters
        .nodes
        .iter()
        .map(|&id| node(&fixture.helper, HELPER_FILE, id))
        .collect::<Vec<_>>();
    assert_eq!(helper_parameters.len(), 1);
    let mut outer_signatures = Vec::new();
    for property in properties {
        assert_eq!(context.get_type_at_location(property.call).unwrap(), string);
        assert_eq!(resolved(context, property.call), string);
        outer_signatures.push(assert_signature(
            context,
            property.call,
            helper,
            &helper_parameters,
            0,
            string,
        ));
        let raw = bound_symbol(context, property.declaration);
        let owner = bound_symbol(context, object);
        let record = context.store().symbol(raw).unwrap();
        assert_eq!(record.name(), InternalSymbolName::Computed.as_ref());
        assert_eq!(record.parent(), Some(owner));
        assert_eq!(record.declarations(), Some(&[property.declaration][..]));
        assert_eq!(record.value_declaration(), Some(property.declaration));
        assert_eq!(
            fixture
                .source
                .arena
                .get(property.computed.node)
                .unwrap()
                .parent,
            Some(property.declaration.node)
        );
        assert_eq!(
            fixture.source.arena.get(property.call.node).unwrap().parent,
            Some(property.computed.node)
        );
    }
    assert_eq!(outer_signatures[0], outer_signatures[1]);

    let tag = properties[0].argument;
    let NodeData::TaggedTemplateExpression(tagged) =
        &fixture.source.arena.get(tag.node).unwrap().data
    else {
        panic!("the first key must retain String.raw as a real tagged template")
    };
    assert!(tagged.type_arguments.is_none());
    assert_eq!(
        fixture.source.arena.get(tagged.template).unwrap().kind,
        SyntaxKind::NoSubstitutionTemplateLiteral
    );
    let NodeData::PropertyAccessExpression(access) =
        &fixture.source.arena.get(tagged.tag).unwrap().data
    else {
        panic!("the tag must retain its property callee")
    };
    let string_use = node(&fixture.source, SOURCE_FILE, access.expression);
    let string_declaration =
        fixture.library_declaration("lib.es5.d.ts", SyntaxKind::VariableDeclaration, "String");
    assert_eq!(
        context.get_symbol_at_location(string_use).unwrap(),
        Some(bound_symbol(context, string_declaration))
    );
    let raw =
        fixture.library_declaration("lib.es2015.core.d.ts", SyntaxKind::MethodSignature, "raw");
    let (raw_file, core) = fixture.library("lib.es2015.core.d.ts");
    let NodeData::MethodSignatureDeclaration(method) = &core.arena.get(raw.node).unwrap().data
    else {
        unreachable!()
    };
    let raw_parameters = method
        .parameters
        .nodes
        .iter()
        .map(|&id| node(core, raw_file, id))
        .collect::<Vec<_>>();
    assert_eq!(raw_parameters.len(), 2);
    assert_eq!(
        core.arena.get(raw.node).unwrap().parent,
        Some(
            fixture
                .library_declaration(
                    "lib.es2015.core.d.ts",
                    SyntaxKind::InterfaceDeclaration,
                    "StringConstructor",
                )
                .node
        )
    );
    assert_eq!(context.get_type_at_location(tag).unwrap(), string);
    assert_signature(context, tag, raw, &raw_parameters, 1, string);

    let object_type = resolved(context, object);
    let TypeData::Object(object_data) = context.store().type_payload(object_type).unwrap().data()
    else {
        panic!("expected a checked computed-key object")
    };
    assert_eq!(
        context.store().type_payload(object_type).unwrap().symbol(),
        Some(bound_symbol(context, object))
    );
    assert!(
        object_data
            .structured
            .properties
            .as_deref()
            .unwrap()
            .is_empty()
    );
    assert!(
        context
            .store()
            .symbol_table(object_data.structured.members.unwrap())
            .unwrap()
            .is_empty()
    );
    let [index] = object_data.structured.index_infos.as_deref().unwrap() else {
        panic!("broad string calls must produce one string index, not folded names")
    };
    let info = context.store().index_info(*index).unwrap();
    assert_eq!(info.key_type(), string);
    assert_eq!(info.value_type(), string);
    assert_eq!(
        info.components(),
        &[properties[0].declaration, properties[1].declaration]
    );
    assert_eq!(info.declaration(), None);
    assert_eq!(info.index_symbol(), None);
    assert!(!info.is_readonly());

    let (value, read) = fixture.variable("value");
    let read_type = context.get_type_at_location(read).unwrap();
    assert_eq!(context.get_type_at_location(value).unwrap(), read_type);
    let TypeData::Union(union) = context.store().type_payload(read_type).unwrap().data() else {
        panic!("an unchecked index read must retain undefined")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&string));
    assert!(union.union.types.contains(&undefined));
    object_type
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<(
        NodeRef,
        Option<TypeNodeLinks>,
        Option<SymbolNodeLinks>,
        Option<SignatureLinks>,
    )>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    aliases: Vec<(SemanticSymbolId, Option<AliasSymbolLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, fixture: &Fixture) -> Snapshot {
    let nodes = fixture.tracked_nodes();
    let mut symbols = Vec::new();
    for &location in &nodes {
        if let Some(symbol) = context.file(location.file).unwrap().1.symbol(location) {
            let symbol = context.store().get_merged_symbol(symbol).unwrap();
            if !symbols.contains(&symbol) {
                symbols.push(symbol);
            }
        }
    }
    Snapshot {
        counts: counts(context),
        sources: [HELPER_FILE, SOURCE_FILE]
            .into_iter()
            .map(|file| {
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: nodes
            .into_iter()
            .map(|location| {
                (
                    location,
                    context.store().type_node_links(location).cloned(),
                    context.store().symbol_node_links(location).cloned(),
                    context.store().signature_links(location).cloned(),
                )
            })
            .collect(),
        values: symbols
            .iter()
            .map(|&symbol| (symbol, context.store().value_symbol_links(symbol).cloned()))
            .collect(),
        aliases: symbols
            .iter()
            .map(|&symbol| (symbol, context.store().alias_symbol_links(symbol).cloned()))
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
fn computed_key_keeps_real_string_raw_and_imported_call_types() {
    let ordinary_call = r#"normalizeWindowsPath("C:\\a\\..\\")"#;
    assert_eq!(SOURCE.matches(ordinary_call).count(), 1);
    let bad_source = SOURCE.replacen(ordinary_call, "normalizeWindowsPath(123)", 1);
    for (bad_argument, source) in [(false, SOURCE), (true, bad_source.as_str())] {
        let fixture = Fixture::new(source);
        let object = fixture.variable("cases").1;
        let properties = properties(&fixture, object);
        for query_first in [false, true] {
            let mut context = fixture.context();
            let source_root = context.source_file(SOURCE_FILE).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source_root)
                    .is_some_and(|links| links.type_checked)
            );
            if query_first {
                context.get_type_at_location(object).unwrap();
            } else {
                context.check_source_file(SOURCE_FILE).unwrap();
            }
            let object_type = assert_types(&fixture, &mut context, object, &properties);
            context.check_source_file(HELPER_FILE).unwrap();
            assert_eq!(
                assert_types(&fixture, &mut context, object, &properties),
                object_type
            );
            if bad_argument {
                assert_eq!(
                    fixture
                        .source
                        .arena
                        .get(properties[1].argument.node)
                        .unwrap()
                        .kind,
                    SyntaxKind::NumericLiteral
                );
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("only the bad helper argument must produce a diagnostic")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2345);
                assert_eq!(diagnostic.node, Some(properties[1].argument));
                assert_eq!(diagnostic.range_override, None);
                assert!(diagnostic.related_information.is_empty());
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Argument of type 'number' is not assignable to parameter of type 'string'."
                );
            } else {
                assert!(
                    context.diagnostics().is_empty(),
                    "{:?}",
                    context.diagnostics()
                );
            }
            let TypeData::Object(data) = context.store().type_payload(object_type).unwrap().data()
            else {
                unreachable!()
            };
            let indexes = data.structured.index_infos.clone();
            let before = snapshot(&context, &fixture);
            for _ in 0..2 {
                context.recheck_source_file(HELPER_FILE).unwrap();
                context.recheck_source_file(SOURCE_FILE).unwrap();
                assert_eq!(
                    assert_types(&fixture, &mut context, object, &properties),
                    object_type
                );
                let TypeData::Object(data) =
                    context.store().type_payload(object_type).unwrap().data()
                else {
                    unreachable!()
                };
                assert_eq!(data.structured.index_infos, indexes);
                assert_eq!(snapshot(&context, &fixture), before);
            }
        }
    }
}
