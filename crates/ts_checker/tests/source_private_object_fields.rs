use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalImportCallMode,
    IntrinsicBootstrapOptions, TypeData, TypeId, ValueSymbolLinks,
    production::CanonicalJsxRuntime,
    types::{ObjectFlags, TypeFlags},
};
use ts_options::{CompilerOptions, JsxEmit, ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_900);
const TSLIB_FILE: FileId = FileId::new(204_901);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$(($name, include_str!(concat!("../../ts_bundled/libs/", $name)))),+]
    };
}

// The real ES6 default library and its complete reference-lib closure.
const LIBRARIES: &[(&str, &str)] = libraries![
    "lib.es6.d.ts",
    "lib.es2015.d.ts",
    "lib.es5.d.ts",
    "lib.decorators.d.ts",
    "lib.decorators.legacy.d.ts",
    "lib.es2015.core.d.ts",
    "lib.es2015.collection.d.ts",
    "lib.es2015.iterable.d.ts",
    "lib.es2015.generator.d.ts",
    "lib.es2015.promise.d.ts",
    "lib.es2015.proxy.d.ts",
    "lib.es2015.reflect.d.ts",
    "lib.es2015.symbol.d.ts",
    "lib.es2015.symbol.wellknown.d.ts",
    "lib.dom.d.ts",
    "lib.dom.iterable.d.ts",
    "lib.es2018.asynciterable.d.ts",
    "lib.webworker.importscripts.d.ts",
    "lib.scripthost.d.ts",
];

// Exact pinned input, including its helper package and fixture-only directive.
const ORIGINAL_FIXTURE: &str = r#"// @target: es6
// @module: commonjs
// @importHelpers: true
// @noTypesAndSymbols: true

// @filename: /privateIdentifierPropertyAccessDestructuringAssignmentES6.ts

class Example {
    #state = { value: 0 };

    update(source: { value: { value: number } }) {
        ({ value: this.#state } = source);
    }
}

new Example().update({ value: { value: 1 } });

export {};

// @filename: /node_modules/tslib/package.json
{
    "name": "tslib",
    "main": "tslib.js",
    "typings": "tslib.d.ts"
}

// @filename: /node_modules/tslib/tslib.d.ts
export declare function __classPrivateFieldGet(a: any, b: any, c: any, d: any): any;

// @filename: /node_modules/tslib/tslib.js
module.exports.__classPrivateFieldGet = function (receiver, state, kind, f) {
    return kind === "m" ? f : kind === "a" ? f.call(receiver) : f ? f.value : state.get(receiver);
};"#;

fn parsed_libraries() -> Vec<ParseResult> {
    for &(_, source) in LIBRARIES {
        for reference in source.lines().filter_map(|line| {
            line.strip_prefix("/// <reference lib=\"")
                .and_then(|line| line.strip_suffix("\" />"))
        }) {
            let path = format!("lib.{reference}.d.ts");
            assert!(LIBRARIES.iter().any(|&(name, _)| name == path));
        }
    }
    LIBRARIES
        .iter()
        .map(|&(_, source)| parse_source_file(source))
        .collect()
}

fn compiler_options(original: bool) -> CompilerOptions {
    let overrides = CompilerOptions {
        target: ScriptTarget::Es2015,
        module: if original {
            ModuleKind::CommonJs
        } else {
            ModuleKind::None
        },
        import_helpers: original,
        ..CompilerOptions::default()
    };
    let names: &[&str] = if original {
        &["target", "module", "importhelpers"]
    } else {
        &["target"]
    };
    let mut options = CompilerOptions::default();
    options.apply_overrides(
        &overrides,
        &names.iter().map(|name| (*name).to_owned()).collect(),
    );
    options
}

fn checker_options(options: &CompilerOptions) -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: options.strict_null_checks,
            exact_optional_property_types: options.exact_optional_property_types,
        },
        strict_bind_call_apply: options.strict_bind_call_apply,
        strict_builtin_iterator_return: options.strict_builtin_iterator_return,
        strict_function_types: options.strict_function_types,
        strict_property_initialization: options.strict_property_initialization,
        use_unknown_in_catch_variables: if options.use_unknown_in_catch_variables_specified {
            options.use_unknown_in_catch_variables
        } else {
            options.strict
        },
        no_implicit_any: options.no_implicit_any,
        no_implicit_this: if options.no_implicit_this_specified {
            options.no_implicit_this
        } else {
            options.strict
        },
        no_unchecked_indexed_access: options.no_unchecked_indexed_access,
        no_unused_locals: options.no_unused_locals,
        no_unused_parameters: options.no_unused_parameters,
        allow_unreachable_code: options.allow_unreachable_code,
        preserve_const_enums: options.preserve_const_enums,
        isolated_modules: options.isolated_modules,
        jsx_runtime: if options.jsx_runtime_module_specifier().is_some() {
            CanonicalJsxRuntime::Automatic
        } else if options.jsx == JsxEmit::React {
            CanonicalJsxRuntime::Classic
        } else {
            CanonicalJsxRuntime::Preserve
        },
        emit_common_js: options.module == ModuleKind::CommonJs,
        module_kind: options.module,
        import_call_mode: match options.module.effective_for_target(options.target) {
            ModuleKind::EsNext | ModuleKind::Preserve => CanonicalImportCallMode::Deferred,
            ModuleKind::Es2015 => CanonicalImportCallMode::Unsupported,
            ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 | ModuleKind::NodeNext => {
                CanonicalImportCallMode::DynamicWithAttributes
            }
            _ => CanonicalImportCallMode::Dynamic,
        },
        no_emit: options.no_emit,
        uses_wildcard_types: options
            .types
            .as_ref()
            .is_some_and(|types| types.iter().any(|name| name == "*")),
        no_error_truncation: options.no_error_truncation,
        check_bigint_target: true,
        name_resolution: CanonicalNameResolverOptions::from(options),
    }
}

fn context<'arena>(
    libraries: &'arena [ParseResult],
    source: &'arena ParseResult,
    tslib: Option<&'arena ParseResult>,
) -> CanonicalCheckerContext<'arena> {
    let original = tslib.is_some();
    let options = compiler_options(original);
    let mut files = libraries
        .iter()
        .enumerate()
        .map(|(index, parsed)| {
            (
                FileId::new(204_800 + u32::try_from(index).unwrap()),
                parsed,
                format!("/{}", LIBRARIES[index].0),
                true,
                true,
                CanonicalModuleState::Script,
            )
        })
        .collect::<Vec<_>>();
    files.push((
        FILE,
        source,
        if original {
            "/privateIdentifierPropertyAccessDestructuringAssignmentES6.ts".to_owned()
        } else {
            "/private-object-fields.ts".to_owned()
        },
        false,
        false,
        if original {
            CanonicalModuleState::External
        } else {
            CanonicalModuleState::Script
        },
    ));
    if let Some(tslib) = tslib {
        files.push((
            TSLIB_FILE,
            tslib,
            "/node_modules/tslib/tslib.d.ts".to_owned(),
            true,
            false,
            CanonicalModuleState::External,
        ));
    }
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, ref path, declaration, library, module) in &files {
        assert!(
            parsed.diagnostics.is_empty(),
            "{path}: {:?}",
            parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"{path}\"")),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    library,
                    module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, ..)| (*file, &parsed.arena))
            .collect(),
        checker_options(&options),
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

#[derive(Clone, Copy)]
struct Field {
    class: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
    property: NodeRef,
    literal: NodeRef,
}

fn field(parsed: &ParseResult, class_name: &str) -> Field {
    let (class, data) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == class_name).then_some((reference(parsed, node), class))
        })
        .unwrap();
    let declaration = data
        .members
        .nodes
        .iter()
        .copied()
        .find(|&node| {
            matches!(&parsed.arena.get(node).unwrap().data, NodeData::PropertyDeclaration(property)
            if matches!(&parsed.arena.get(property.name).unwrap().data,
                NodeData::PrivateIdentifier(name) if name.text == "#state"))
        })
        .unwrap();
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(declaration).unwrap().data
    else {
        unreachable!()
    };
    let initializer = property.initializer.unwrap();
    let NodeData::ObjectLiteralExpression(object) = &parsed.arena.get(initializer).unwrap().data
    else {
        panic!("the private field retains its real object initializer")
    };
    let &[member] = object.properties.nodes.as_slice() else {
        panic!("the control has one mutable object property")
    };
    let NodeData::PropertyAssignment(member_data) = &parsed.arena.get(member).unwrap().data else {
        unreachable!()
    };
    Field {
        class,
        declaration: reference(parsed, declaration),
        name: reference(parsed, property.name),
        initializer: reference(parsed, initializer),
        property: reference(parsed, member),
        literal: reference(parsed, member_data.initializer),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FieldIdentity {
    owner: SemanticSymbolId,
    field: SemanticSymbolId,
    private_name: EscapedName,
    object_owner: SemanticSymbolId,
    source_property: SemanticSymbolId,
    property: SemanticSymbolId,
    initializer: TypeId,
    value: TypeId,
    instance: TypeId,
    constructor: TypeId,
    tables: [SymbolTableId; 3],
}

#[allow(clippy::too_many_lines)] // Keep each field, its object producer, and the widened result in one check.
fn assert_field(
    checker: &mut CanonicalCheckerContext<'_>,
    field: Field,
    primitive: TypeId,
    literal_display: &str,
) -> FieldIdentity {
    let owner = symbol(checker, field.class);
    let private = symbol(checker, field.declaration);
    let object_owner = symbol(checker, field.initializer);
    let source_property = symbol(checker, field.property);
    let value = checker.get_type_at_location(field.name).unwrap();
    let initializer = checker.get_type_at_location(field.initializer).unwrap();
    assert_ne!(value, initializer);
    assert_eq!(checker.get_class_query_member_type(private), Ok(value));
    assert_eq!(
        checker.get_symbol_at_location(field.name),
        Ok(Some(private))
    );
    let literal = checker.get_type_at_location(field.literal).unwrap();
    assert_eq!(checker.type_to_string(literal).unwrap(), literal_display);
    assert_ne!(literal, primitive);

    let members = checker.get_nongeneric_class_members(owner).unwrap();
    assert!(members.declared_instance_properties().contains(&private));
    let instance = members.shells().instance_type();
    let constructor = members.shells().value_type();
    let store = checker.store();
    let class = store.symbol(owner).unwrap();
    let table = class.members().unwrap();
    let field_record = store.symbol(private).unwrap();
    let private_name = field_record.name().to_owned();
    assert!(private_name.as_ref().is_private_identifier());
    let private_owner = store
        .symbol_store()
        .assigned_global_symbol_id(owner)
        .unwrap();
    assert_eq!(
        private_name.as_bytes().strip_prefix(b"\xFE#"),
        Some(format!("{private_owner}@#state").as_bytes())
    );
    assert_eq!(field_record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(field_record.check_flags(), CheckFlags::NONE);
    assert_eq!(field_record.parent(), Some(owner));
    assert_eq!(field_record.value_declaration(), Some(field.declaration));
    assert_eq!(
        field_record.declarations(),
        Some([field.declaration].as_slice())
    );
    assert_eq!(
        store
            .symbol_table(table)
            .unwrap()
            .get(private_name.as_ref()),
        Some(private)
    );
    assert!(
        store
            .symbol_table(table)
            .unwrap()
            .get_source("#state")
            .is_none()
    );
    assert_eq!(
        store.value_symbol_links(private),
        Some(&ValueSymbolLinks {
            resolved_type: Some(value),
            ..ValueSymbolLinks::default()
        })
    );
    assert_ne!(object_owner, private);
    assert_ne!(object_owner, owner);
    assert_eq!(
        store.symbol(object_owner).unwrap().declarations(),
        Some([field.initializer].as_slice())
    );
    let source = store.symbol(source_property).unwrap();
    assert_eq!(source.flags(), SymbolFlags::PROPERTY);
    assert_eq!(source.name().as_utf8(), Some("value"));
    assert_eq!(source.parent(), Some(object_owner));
    assert_eq!(source.declarations(), Some([field.property].as_slice()));

    let fresh = store.type_payload(initializer).unwrap();
    assert_eq!(fresh.flags(), TypeFlags::OBJECT);
    assert_eq!(fresh.symbol(), Some(object_owner));
    assert!(
        fresh
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
    );
    let TypeData::Object(fresh_object) = fresh.data() else {
        panic!("the initializer is an object")
    };
    let fresh_table = fresh_object.structured.members.unwrap();
    let property = store
        .symbol_table(fresh_table)
        .unwrap()
        .get_source("value")
        .unwrap();
    assert_eq!(
        fresh_object.structured.properties.as_deref(),
        Some([property].as_slice())
    );
    assert_ne!(property, source_property);
    let published = store.symbol(property).unwrap();
    assert_eq!(
        published.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(published.parent(), Some(object_owner));
    assert_eq!(published.declarations(), source.declarations());
    assert_eq!(published.value_declaration(), source.value_declaration());
    assert_eq!(
        store.value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(primitive),
            target: Some(source_property),
            ..ValueSymbolLinks::default()
        })
    );

    let widened = store.type_payload(value).unwrap();
    assert_eq!(widened.flags(), TypeFlags::OBJECT);
    assert_eq!(widened.symbol(), Some(object_owner));
    assert_eq!(
        widened.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Object(widened_object) = widened.data() else {
        panic!("the widened field is an object")
    };
    let widened_table = widened_object.structured.members.unwrap();
    assert_ne!(fresh_table, widened_table);
    assert_eq!(
        store
            .symbol_table(widened_table)
            .unwrap()
            .get_source("value"),
        Some(property)
    );
    assert_eq!(
        widened_object.structured.properties.as_deref(),
        Some([property].as_slice())
    );
    assert!(widened_object.target.is_none());
    assert!(widened_object.mapper.is_none());
    assert!(widened_object.structured.signatures.is_none());
    assert!(widened_object.structured.index_infos.is_none());
    FieldIdentity {
        owner,
        field: private,
        private_name,
        object_owner,
        source_property,
        property,
        initializer,
        value,
        instance,
        constructor,
        tables: [table, fresh_table, widened_table],
    }
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    reference(parsed, node),
                    reference(parsed, variable.name),
                    reference(parsed, variable.initializer.unwrap()),
                )
            })
        })
        .unwrap()
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.merged_symbol_len(),
            store.symbol_store().symbol_table_len(),
        ],
        checker.global_types().clone(),
        checker.diagnostics().clone(),
        store.relation_state_snapshot(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        source
            .arena
            .iter()
            .map(|(node, _)| {
                let node = reference(source, node);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .filter(|(_, record)| {
                record
                    .declarations()
                    .is_some_and(|nodes| nodes.iter().any(|node| node.file == FILE))
            })
            .map(|(symbol, record)| {
                let links = store.value_symbol_links(symbol).cloned();
                let type_ = links.as_ref().and_then(|links| links.resolved_type);
                (
                    symbol,
                    record.clone(),
                    [record.members(), record.exports()].map(|table| {
                        table.map(|table| (table, store.symbol_table(table).unwrap().clone()))
                    }),
                    links,
                    store.declared_type_links(symbol).cloned(),
                    type_.map(|type_| (type_, format!("{:?}", store.type_payload(type_).unwrap()))),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[test]
fn private_object_fields_widen_members_and_replay_reads_in_both_query_orders() {
    let libraries = parsed_libraries();
    let source = parse_source_file(concat!(
        "class Example { #state = { value: 0 }; read() { return this.#state; } }\n",
        "const example = new Example();\n",
        "const state = example.read();\n",
        "const good: number = state.value;\n",
        "const bad: string = state.value;\n",
    ));
    let field = field(&source, "Example");
    let (state, _, call) = variable(&source, "state");
    let (_, _, good) = variable(&source, "good");
    let (_, bad_name, bad) = variable(&source, "bad");
    for query_first in [false, true] {
        let mut checker = context(&libraries, &source, None);
        let cold = query_first.then(|| checker.get_type_at_location(field.name).unwrap());
        checker.check_source_file(FILE).unwrap();
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let identity = assert_field(&mut checker, field, number, "0");
        assert!(cold.is_none_or(|type_| type_ == identity.value));
        assert_eq!(
            checker.type_to_string(identity.value).unwrap(),
            "{ value: number; }"
        );
        assert_eq!(checker.get_type_at_location(call), Ok(identity.value));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol(&checker, state))
                .unwrap()
                .resolved_type,
            Some(identity.value)
        );
        for read in [good, bad] {
            assert_eq!(checker.get_type_at_location(read), Ok(number));
            assert_eq!(
                checker.get_symbol_at_location(read),
                Ok(Some(identity.property))
            );
        }
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!(
                "only the incompatible value read is reported: {:?}",
                checker.diagnostics()
            )
        };
        assert_eq!(diagnostic.node, Some(bad_name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(diagnostic.related_information.is_empty());
        let before = snapshot(&checker, &source);
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(assert_field(&mut checker, field, number, "0"), identity);
            assert_eq!(checker.get_type_at_location(call), Ok(identity.value));
            assert_eq!(checker.get_type_at_location(good), Ok(number));
            assert_eq!(checker.get_type_at_location(bad), Ok(number));
            assert_eq!(snapshot(&checker, &source), before);
        }
    }
}

#[test]
fn same_spelled_private_object_fields_keep_distinct_class_owners() {
    let libraries = parsed_libraries();
    let source = parse_source_file(concat!(
        "class First { #state = { value: 0 }; }\n",
        "class Second { #state = { value: 1 }; }\n",
        "class LabelState { #state = { value: 'ready' }; }\n",
    ));
    let fields = ["First", "Second", "LabelState"].map(|name| field(&source, name));
    for order in [[0, 1, 2], [2, 1, 0]] {
        for query_first in [false, true] {
            let mut checker = context(&libraries, &source, None);
            if query_first {
                checker.get_type_at_location(fields[order[0]].name).unwrap();
            } else {
                checker.check_source_file(FILE).unwrap();
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let primitives = [
                bootstrap.number_type,
                bootstrap.number_type,
                bootstrap.string_type,
            ];
            let literals = ["0", "1", "\"ready\""];
            let identities = fields
                .into_iter()
                .enumerate()
                .map(|(index, field)| {
                    assert_field(&mut checker, field, primitives[index], literals[index])
                })
                .collect::<Vec<_>>();
            checker.check_source_file(FILE).unwrap();
            assert!(checker.diagnostics().is_empty());
            for (left, right) in [(0, 1), (1, 0)] {
                assert_ne!(identities[left].owner, identities[right].owner);
                assert_ne!(identities[left].field, identities[right].field);
                assert_ne!(
                    identities[left].private_name,
                    identities[right].private_name
                );
                assert_ne!(
                    identities[left].object_owner,
                    identities[right].object_owner
                );
                assert_ne!(identities[left].property, identities[right].property);
                assert_eq!(
                    checker.is_type_assignable_to(identities[left].value, identities[right].value),
                    Ok(true)
                );
                assert_eq!(
                    checker.is_type_assignable_to(
                        identities[left].instance,
                        identities[right].instance
                    ),
                    Ok(false)
                );
            }
            assert_eq!(
                checker.type_to_string(identities[2].value).unwrap(),
                "{ value: string; }"
            );
            let before = snapshot(&checker, &source);
            for _ in 0..2 {
                checker.recheck_source_file(FILE).unwrap();
                for index in order {
                    assert_eq!(
                        assert_field(
                            &mut checker,
                            fields[index],
                            primitives[index],
                            literals[index]
                        ),
                        identities[index]
                    );
                }
                for (left, right) in [(0, 1), (1, 0)] {
                    assert_eq!(
                        checker
                            .is_type_assignable_to(identities[left].value, identities[right].value),
                        Ok(true)
                    );
                    assert_eq!(
                        checker.is_type_assignable_to(
                            identities[left].instance,
                            identities[right].instance
                        ),
                        Ok(false)
                    );
                }
                assert_eq!(snapshot(&checker, &source), before);
            }
        }
    }
}

fn original_fixture_units() -> Vec<(&'static str, String)> {
    let mut directives = Vec::new();
    let mut units = Vec::<(&str, String)>::new();
    // Match the fixture runner's leading-blank and newline rules without dropping any virtual file.
    for line in ORIGINAL_FIXTURE.split('\n') {
        if let Some(path) = line.strip_prefix("// @filename: ") {
            units.push((path, String::new()));
        } else if let Some(directive) = line.strip_prefix("// @") {
            directives.push(directive.split_once(": ").unwrap());
        } else if let Some((_, source)) = units.last_mut() {
            if !source.is_empty() {
                source.push('\n');
            }
            source.push_str(line);
        }
    }
    assert_eq!(
        directives,
        [
            ("target", "es6"),
            ("module", "commonjs"),
            ("importHelpers", "true"),
            ("noTypesAndSymbols", "true")
        ]
    );
    assert_eq!(
        units.iter().map(|(path, _)| *path).collect::<Vec<_>>(),
        [
            "/privateIdentifierPropertyAccessDestructuringAssignmentES6.ts",
            "/node_modules/tslib/package.json",
            "/node_modules/tslib/tslib.d.ts",
            "/node_modules/tslib/tslib.js",
        ]
    );
    units
}

#[derive(Debug, Eq, PartialEq)]
struct DestructuringIdentity {
    parameter: SemanticSymbolId,
    source: TypeId,
    selected: SemanticSymbolId,
    assigned: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the source selection and private target together.
fn assert_original_private_write(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    update: NodeRef,
    field: &FieldIdentity,
) -> DestructuringIdentity {
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(update.node).unwrap().data else {
        unreachable!()
    };
    let &[parameter] = method.parameters.nodes.as_slice() else {
        panic!("the update method keeps its one source parameter")
    };
    let parameter = reference(parsed, parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let parameter_name = reference(parsed, parameter_data.name);
    let annotation = reference(parsed, parameter_data.type_.unwrap());
    let parameter_symbol = symbol(checker, parameter);
    let source = checker.get_type_from_type_node(annotation).unwrap();
    assert_eq!(
        checker.file(FILE).unwrap().1.container(parameter),
        Some(update)
    );
    let parameter_record = checker.store().symbol(parameter_symbol).unwrap();
    assert_eq!(
        parameter_record.flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    );
    assert_eq!(parameter_record.parent(), None);
    assert_eq!(
        parameter_record.declarations(),
        Some([parameter].as_slice())
    );
    assert_eq!(parameter_record.value_declaration(), Some(parameter));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .resolved_type,
        Some(source)
    );

    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("the source parameter keeps its object annotation")
    };
    let &[selected] = literal.members.nodes.as_slice() else {
        panic!("the source annotation keeps its one value property")
    };
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(selected).unwrap().data else {
        unreachable!()
    };
    let selected = reference(parsed, selected);
    let selected_symbol = symbol(checker, selected);
    let selected_annotation = reference(parsed, property.type_.unwrap());
    let assigned = checker
        .get_type_from_type_node(selected_annotation)
        .unwrap();
    let source_owner = symbol(checker, annotation);
    let source_record = checker.store().type_payload(source).unwrap();
    assert_eq!(source_record.symbol(), Some(source_owner));
    let TypeData::Object(object) = source_record.data() else {
        panic!("the source keeps its binder-owned object type")
    };
    assert_eq!(
        object.structured.properties.as_deref(),
        Some([selected_symbol].as_slice())
    );
    assert_eq!(
        checker
            .store()
            .symbol_table(object.structured.members.unwrap())
            .unwrap()
            .get_source("value"),
        Some(selected_symbol)
    );
    let property_record = checker.store().symbol(selected_symbol).unwrap();
    assert_eq!(property_record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(property_record.name().as_utf8(), Some("value"));
    assert_eq!(property_record.parent(), Some(source_owner));
    assert_eq!(property_record.declarations(), Some([selected].as_slice()));
    assert_eq!(property_record.value_declaration(), Some(selected));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(selected_symbol)
            .unwrap()
            .resolved_type,
        Some(assigned)
    );
    assert_eq!(
        checker.store().type_payload(assigned).unwrap().symbol(),
        Some(symbol(checker, selected_annotation))
    );
    assert_ne!(source, assigned);
    assert_ne!(assigned, field.value);
    assert_ne!(selected_symbol, field.field);

    let NodeData::Block(body) = &parsed.arena.get(method.body.unwrap()).unwrap().data else {
        unreachable!()
    };
    let &[statement] = body.statements.nodes.as_slice() else {
        panic!("the method keeps its one destructuring assignment")
    };
    let NodeData::ExpressionStatement(statement) = &parsed.arena.get(statement).unwrap().data
    else {
        unreachable!()
    };
    let parentheses = reference(parsed, statement.expression);
    let NodeData::ParenthesizedExpression(inner) =
        &parsed.arena.get(parentheses.node).unwrap().data
    else {
        panic!("the original assignment keeps its parentheses")
    };
    let assignment = reference(parsed, inner.expression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let rhs = reference(parsed, binary.right);
    assert!(matches!(&parsed.arena.get(rhs.node).unwrap().data,
        NodeData::Identifier(identifier) if identifier.text == "source"));
    let NodeData::ObjectLiteralExpression(pattern) = &parsed.arena.get(binary.left).unwrap().data
    else {
        panic!("the assignment keeps its object pattern")
    };
    let &[property] = pattern.properties.nodes.as_slice() else {
        panic!("the assignment selects one source property")
    };
    let NodeData::PropertyAssignment(property) = &parsed.arena.get(property).unwrap().data else {
        unreachable!()
    };
    assert!(matches!(&parsed.arena.get(property.name).unwrap().data,
        NodeData::Identifier(identifier) if identifier.text == "value"));
    let target = reference(parsed, property.initializer);
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(target.node).unwrap().data
    else {
        panic!("the selected value is written to the real private field")
    };
    let receiver = reference(parsed, access.expression);
    let name = reference(parsed, access.name);
    assert_eq!(
        parsed.arena.get(receiver.node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert!(matches!(&parsed.arena.get(name.node).unwrap().data,
        NodeData::PrivateIdentifier(identifier) if identifier.text == "#state"));
    assert_eq!(
        checker.file(FILE).unwrap().1.flow_container(target),
        Some(update)
    );
    assert_eq!(
        checker
            .store()
            .symbol_node_links(target)
            .unwrap()
            .resolved_symbol,
        Some(field.field)
    );
    let TypeData::Interface(class) = checker.store().type_payload(field.instance).unwrap().data()
    else {
        panic!("the private target keeps its real class instance")
    };
    let this_type = class.this_type.unwrap();
    for (node, expected) in [
        (parameter_name, source),
        (rhs, source),
        (assignment, source),
        (parentheses, source),
        (target, field.value),
        (receiver, this_type),
    ] {
        assert_eq!(
            checker.store().type_node_links(node).unwrap().resolved_type,
            Some(expected)
        );
        assert_eq!(checker.get_type_at_location(node), Ok(expected));
    }
    assert_eq!(checker.get_type_at_location(name), Ok(field.value));
    for node in [parameter_name, rhs] {
        assert_eq!(
            checker.get_symbol_at_location(node),
            Ok(Some(parameter_symbol))
        );
    }
    for node in [target, name] {
        assert_eq!(checker.get_symbol_at_location(node), Ok(Some(field.field)));
    }
    let graph = checker.file(FILE).unwrap().1.flow_graph();
    assert_eq!(
        graph
            .nodes()
            .iter()
            .filter(|flow| {
                flow.flags.contains(FlowFlags::ASSIGNMENT)
                    && flow.payload == Some(FlowNodePayload::Ast(target))
            })
            .count(),
        1
    );
    DestructuringIdentity {
        parameter: parameter_symbol,
        source,
        selected: selected_symbol,
        assigned,
    }
}

#[test]
fn original_private_destructuring_fixture_checks_real_field_and_selected_write() {
    let units = original_fixture_units();
    let options = compiler_options(true);
    assert_eq!(options.target, ScriptTarget::Es2015);
    assert_eq!(options.module, ModuleKind::CommonJs);
    assert!(options.module_specified);
    assert!(options.import_helpers);
    assert!(!options.allow_js);
    assert!(!options.no_emit);
    assert!(!options.no_lib);
    assert!(options.lib.is_none());
    assert!(units[1].1.contains("\"typings\": \"tslib.d.ts\""));
    assert!(units[2].1.contains("__classPrivateFieldGet"));
    assert!(!units[2].1.contains("__classPrivateFieldSet"));
    assert!(units[3].1.contains("module.exports.__classPrivateFieldGet"));
    // A separate Program test owns TS6504 and TS2343. This checker test retains every
    // virtual file, but does not parse the JavaScript root as TypeScript or check helper imports.
    let libraries = parsed_libraries();
    let source = parse_source_file(&units[0].1);
    let tslib = parse_source_file(&units[2].1);
    let update = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::MethodDeclaration(_))
                .then_some(reference(&source, node))
        })
        .unwrap();
    let NodeData::MethodDeclaration(method) = &source.arena.get(update.node).unwrap().data else {
        unreachable!()
    };
    let &[parameter] = method.parameters.nodes.as_slice() else {
        panic!("the original update method retains its one source parameter")
    };
    let NodeData::ParameterDeclaration(parameter) = &source.arena.get(parameter).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        source.arena.get(parameter.type_.unwrap()).unwrap().kind,
        SyntaxKind::TypeLiteral
    );
    let field = field(&source, "Example");
    let mut checker = context(&libraries, &source, Some(&tslib));
    assert_eq!(
        checker.options().name_resolution.emit_target,
        options.target
    );
    assert_eq!(checker.options().module_kind, options.module);
    assert!(checker.options().emit_common_js);
    assert_eq!(checker.options().no_emit, options.no_emit);
    assert_eq!(
        checker.options().intrinsic.strict_null_checks,
        options.strict_null_checks
    );
    assert_eq!(
        checker.options().strict_property_initialization,
        options.strict_property_initialization
    );
    assert_eq!(checker.options().no_implicit_any, options.no_implicit_any);
    assert_eq!(checker.check_source_file(FILE), Ok(()));
    assert!(checker.diagnostics().is_empty());
    let private = symbol(&checker, field.declaration);
    assert!(
        checker
            .store()
            .symbol(private)
            .unwrap()
            .name()
            .is_private_identifier()
    );
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let identity = assert_field(&mut checker, field, number, "0");
    assert_eq!(identity.field, private);
    let write = assert_original_private_write(&mut checker, &source, update, &identity);
    let before = snapshot(&checker, &source);
    for _ in 0..2 {
        assert_eq!(checker.check_source_file(FILE), Ok(()));
        assert_eq!(assert_field(&mut checker, field, number, "0"), identity);
        assert_eq!(
            assert_original_private_write(&mut checker, &source, update, &identity),
            write
        );
        assert_eq!(snapshot(&checker, &source), before);
    }
}
