use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(211_640);
const DECORATORS: FileId = FileId::new(211_641);
const LEGACY: FileId = FileId::new(211_642);
const AUGMENTATION: FileId = FileId::new(211_643);
const CONSUMER: FileId = FileId::new(211_644);

const PROVIDER: &str = concat!(
    "export {};\n",
    "declare global {\n",
    "  interface AmbientValue { marker: string; }\n",
    "  var AmbientValue: number;\n",
    "}\n",
);
const SOURCE: &str = concat!(
    "export {};\n",
    "type World = typeof globalThis;\n",
    "type Numeric = typeof globalThis.Infinity;\n",
    "const whole = globalThis;\n",
    "const value: number = globalThis.Infinity;\n",
    "const bad: string = globalThis.Infinity;\n",
);

struct Inputs {
    library: ParseResult,
    decorators: ParseResult,
    legacy: ParseResult,
    augmentation: ParseResult,
    consumer: ParseResult,
}

impl Inputs {
    fn new() -> Self {
        Self {
            library: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.d.ts"
            )),
            legacy: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.legacy.d.ts"
            )),
            augmentation: parse_source_file(PROVIDER),
            consumer: parse_source_file(SOURCE),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let sources = [
            (LIBRARY, &self.library, "/lib.es5.d.ts", true, true),
            (
                DECORATORS,
                &self.decorators,
                "/lib.decorators.d.ts",
                true,
                true,
            ),
            (
                LEGACY,
                &self.legacy,
                "/lib.decorators.legacy.d.ts",
                true,
                true,
            ),
            (
                AUGMENTATION,
                &self.augmentation,
                "/augmentation.d.ts",
                true,
                false,
            ),
            (CONSUMER, &self.consumer, "/consumer.ts", false, false),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, declaration, library) in sources {
            assert!(parsed.diagnostics.is_empty(), "{path}");
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        library,
                        if library {
                            CanonicalModuleState::Script
                        } else {
                            CanonicalModuleState::External
                        },
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|(file, parsed, ..)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_function_types: true,
                no_implicit_any: true,
                no_emit: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.diagnostics().is_empty());
        context
    }
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::ModuleDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn alias_type(parsed: &ParseResult, name: &str) -> NodeRef {
    let node = declaration(parsed, CONSUMER, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(node.arena, node.file, data.type_)
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let node = declaration(parsed, CONSUMER, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(node.arena, node.file, data.initializer.unwrap())
}

fn global(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let record = store.symbol(owner).unwrap();
    let TypeData::Object(global) = store
        .type_payload(context.global_types().global_this_value_type)
        .unwrap()
        .data()
    else {
        panic!("globalThis keeps its canonical object")
    };
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        ],
        global.clone(),
        (
            record.flags(),
            record.parent(),
            record.declarations().unwrap().to_vec(),
            record.value_declaration(),
            store.value_symbol_links(owner).cloned(),
            store.declared_type_links(owner).cloned(),
        ),
        [AUGMENTATION, CONSUMER]
            .into_iter()
            .flat_map(|file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        context.diagnostics().clone(),
        store.relation_state_snapshot(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the source owners, both query orders, and replay together.
fn global_this_table_keeps_augmentation_owned_interface_values_and_replays() {
    let inputs = Inputs::new();
    let interface = declaration(
        &inputs.augmentation,
        AUGMENTATION,
        SyntaxKind::InterfaceDeclaration,
        "AmbientValue",
    );
    let variable = declaration(
        &inputs.augmentation,
        AUGMENTATION,
        SyntaxKind::VariableDeclaration,
        "AmbientValue",
    );
    let module = declaration(
        &inputs.augmentation,
        AUGMENTATION,
        SyntaxKind::ModuleDeclaration,
        "global",
    );
    for query_first in [false, true] {
        let mut context = inputs.context();
        let table_symbol = global(&context, "AmbientValue");
        let owner = context.store().get_merged_symbol(table_symbol).unwrap();
        let bound = context.file(AUGMENTATION).unwrap().1;
        let module_owner = bound.symbol(module).unwrap();
        let NodeData::ModuleDeclaration(data) =
            &inputs.augmentation.arena.get(module.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(data.keyword, SyntaxKind::GlobalKeyword);
        let module_name = NodeRef::new(module.arena, module.file, data.name);
        assert!(
            bound
                .module_augmentations()
                .iter()
                .any(|origin| origin.name() == module_name)
        );
        for declaration in [interface, variable] {
            let raw = bound.symbol(declaration).unwrap();
            assert_eq!(context.store().get_merged_symbol(raw), Some(owner));
            assert_eq!(
                context.store().symbol(raw).unwrap().parent(),
                Some(module_owner)
            );
        }
        let record = context.store().symbol(owner).unwrap();
        assert_eq!(
            record.flags().without(SymbolFlags::TRANSIENT),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        assert_eq!(record.parent(), Some(module_owner));
        assert_eq!(
            record.declarations(),
            Some([interface, variable].as_slice())
        );
        assert_eq!(record.value_declaration(), Some(variable));
        let exports = context
            .store()
            .symbol(module_owner)
            .unwrap()
            .exports()
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("AmbientValue"),
            Some(bound.symbol(interface).unwrap()),
        );

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let world = context.global_types().global_this_value_type;
        let numeric = alias_type(&inputs.consumer, "Numeric");
        if query_first {
            assert_eq!(context.get_type_from_type_node(numeric), Ok(number));
        }
        context.check_source_file(CONSUMER).unwrap();
        assert_eq!(context.get_type_from_type_node(numeric), Ok(number));
        assert_eq!(
            context.get_type_from_type_node(alias_type(&inputs.consumer, "World")),
            Ok(world),
        );
        assert_eq!(
            context.get_type_at_location(initializer(&inputs.consumer, "whole")),
            Ok(world)
        );
        for name in ["value", "bad"] {
            assert_eq!(
                context.get_type_at_location(initializer(&inputs.consumer, name)),
                Ok(number),
            );
        }
        let TypeData::Object(object) = context.store().type_payload(world).unwrap().data() else {
            panic!("globalThis keeps its canonical object")
        };
        assert_eq!(
            context
                .store()
                .symbol_table(object.structured.members.unwrap())
                .unwrap()
                .get_source("AmbientValue"),
            Some(table_symbol),
        );
        assert!(
            object
                .structured
                .properties
                .as_deref()
                .unwrap()
                .contains(&table_symbol)
        );
        // Table materialization must not demand this augmentation's value annotation.
        // Querying that value is a separate, unsupported value-planner path.
        assert!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        let record = context.store().symbol(owner).unwrap();
        assert_eq!(record.parent(), Some(module_owner));
        assert_eq!(
            record.declarations(),
            Some([interface, variable].as_slice())
        );
        assert_eq!(record.value_declaration(), Some(variable));

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected only the number-to-string assignment diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        let bad = declaration(
            &inputs.consumer,
            CONSUMER,
            SyntaxKind::VariableDeclaration,
            "bad",
        );
        let NodeData::VariableDeclaration(data) =
            &inputs.consumer.arena.get(bad.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            diagnostic.node,
            Some(NodeRef::new(bad.arena, bad.file, data.name))
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );

        let before = snapshot(&context, owner);
        for _ in 0..2 {
            context.recheck_source_file(CONSUMER).unwrap();
            assert_eq!(context.get_type_from_type_node(numeric), Ok(number));
            assert_eq!(
                context.get_type_at_location(initializer(&inputs.consumer, "value")),
                Ok(number),
            );
            assert_eq!(snapshot(&context, owner), before);
        }
    }
}
