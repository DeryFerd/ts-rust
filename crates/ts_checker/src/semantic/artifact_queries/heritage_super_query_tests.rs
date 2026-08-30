use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::{CanonicalArtifactQueryError, CanonicalCheckerContext};
use crate::semantic::{CanonicalCheckerOptions, SymbolNodeLinks, TypeNodeLinks};

// Keep the upstream accessOverriddenBaseClassMember1.ts source, including CRLF.
const POINT_SOURCE: &str = concat!(
    "// @target: es2015\r\n",
    "class Point {\r\n",
    "    constructor(public x: number, public y: number) { }\r\n",
    "    public toString() {\r\n",
    "        return \"x=\" + this.x + \" y=\" + this.y;\r\n",
    "    }\r\n",
    "}\r\n",
    "class ColoredPoint extends Point {\r\n",
    "    constructor(x: number, y: number, public color: string) {\r\n",
    "        super(x, y);\r\n",
    "    }\r\n",
    "    public toString() {\r\n",
    "        return super.toString() + \" color=\" + this.color;\r\n",
    "    }\r\n",
    "}\r\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty());
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/accessOverriddenBaseClassMember1.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ts_options::ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn locations(parsed: &ParseResult, file: FileId) -> [NodeRef; 3] {
    let heritage = parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::ExpressionWithTypeArguments(reference) = &node.data else {
                return None;
            };
            Some(NodeRef::new(parsed.arena.id(), file, reference.expression))
        })
        .unwrap();
    let supers = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::SuperKeyword).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(supers.len(), 2);
    [heritage, supers[0], supers[1]]
}

#[test]
fn heritage_super_queries_keep_original_types_symbols_and_warm_identity() {
    for first in 0..3 {
        for symbol_first in [false, true] {
            let parsed = parse_source_file(POINT_SOURCE);
            let file = FileId::new(202_701);
            let mut context = context(&parsed, file);
            let nodes = locations(&parsed, file);
            if symbol_first {
                context.get_symbol_at_location(nodes[first]).unwrap();
            } else {
                context.get_type_at_location(nodes[first]).unwrap();
            }
            let base = context.get_symbol_at_location(nodes[0]).unwrap().unwrap();
            let instance = context.get_declared_type_of_symbol(base).unwrap();
            let value = context
                .store()
                .value_symbol_links(base)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.get_type_at_location(nodes[0]), Ok(instance));
            assert_eq!(context.get_type_at_location(nodes[1]), Ok(value));
            let receiver = context.get_type_at_location(nodes[2]).unwrap();
            assert_ne!(receiver, value);
            for (node, expected) in nodes.into_iter().zip(["Point", "typeof Point", "Point"]) {
                assert_eq!(context.get_symbol_at_location(node), Ok(Some(base)));
                let type_ = context.get_type_at_location(node).unwrap();
                assert_eq!(context.type_to_string(type_).unwrap(), expected);
            }
            assert!(context.diagnostics().is_empty());
            let types = nodes.map(|node| context.get_type_at_location(node).unwrap());
            let type_links = nodes.map(|node| context.store().type_node_links(node).cloned());
            let symbol_links = nodes.map(|node| context.store().symbol_node_links(node).cloned());
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                for (node, type_) in nodes.into_iter().zip(types) {
                    assert_eq!(context.get_symbol_at_location(node), Ok(Some(base)));
                    assert_eq!(context.get_type_at_location(node), Ok(type_));
                }
                assert_eq!(
                    nodes.map(|node| context.store().type_node_links(node).cloned()),
                    type_links
                );
                assert_eq!(
                    nodes.map(|node| context.store().symbol_node_links(node).cloned()),
                    symbol_links
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths()
                    ),
                    before
                );
                assert!(context.diagnostics().is_empty());
            }
        }
    }
}

#[test]
fn heritage_super_queries_reject_wrong_cached_type_roles_without_writes() {
    let parsed = parse_source_file(POINT_SOURCE);
    let file = FileId::new(202_702);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    let nodes = locations(&parsed, file);
    let instance = context.get_type_at_location(nodes[0]).unwrap();
    let value = context.get_type_at_location(nodes[1]).unwrap();
    let receiver = context.get_type_at_location(nodes[2]).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    for (node, wrong) in [
        (nodes[0], string),
        (nodes[1], receiver),
        (nodes[2], value),
        (nodes[2], instance),
    ] {
        let saved = context.store().type_node_links(node).cloned().unwrap();
        assert!(context.store_mut_for_test().set_type_node_links(
            node,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            }
        ));
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_type_at_location(node),
                Err(CanonicalArtifactQueryError::InvalidType { node, type_: wrong })
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
            assert_eq!(
                context.store().type_node_links(node).unwrap().resolved_type,
                Some(wrong)
            );
            assert!(context.diagnostics().is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(node, saved)
        );
        assert_eq!(context.get_type_at_location(nodes[0]), Ok(instance));
        assert_eq!(context.get_type_at_location(nodes[1]), Ok(value));
        assert_eq!(context.get_type_at_location(nodes[2]), Ok(receiver));
    }
}

#[test]
fn heritage_super_queries_reject_wrong_symbol_owner_and_foreign_nodes() {
    let parsed = parse_source_file(POINT_SOURCE);
    let file = FileId::new(202_703);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    let nodes = locations(&parsed, file);
    let owner = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name.and_then(|name| parsed.arena.get(name))?;
            matches!(&name.data, NodeData::Identifier(name) if name.text == "ColoredPoint")
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let derived = context.file(file).unwrap().1.symbol(owner).unwrap();
    let unknown = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .unknown_symbol;
    let base = context.get_symbol_at_location(nodes[0]).unwrap().unwrap();
    for (node, wrong) in nodes
        .into_iter()
        .flat_map(|node| [derived, unknown].map(|symbol| (node, symbol)))
    {
        let saved = context
            .store()
            .symbol_node_links(node)
            .cloned()
            .unwrap_or_default();
        assert!(context.store_mut_for_test().set_symbol_node_links(
            node,
            SymbolNodeLinks {
                resolved_symbol: Some(wrong)
            }
        ));
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_type_at_location(node),
                Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node,
                    symbol: wrong
                })
            );
            assert_eq!(
                context.get_symbol_at_location(node),
                Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node,
                    symbol: wrong
                })
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .unwrap()
                    .resolved_symbol,
                Some(wrong)
            );
            assert!(context.diagnostics().is_empty());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_node_links(node, saved)
        );
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(base)));
    }
    let foreign = parse_source_file(POINT_SOURCE);
    let foreign_node = NodeRef::new(foreign.arena.id(), file, nodes[0].node);
    assert_eq!(
        context.get_type_at_location(foreign_node),
        Err(CanonicalArtifactQueryError::ForeignNode(foreign_node))
    );
    assert_eq!(
        context.get_symbol_at_location(foreign_node),
        Err(CanonicalArtifactQueryError::ForeignNode(foreign_node))
    );
}
