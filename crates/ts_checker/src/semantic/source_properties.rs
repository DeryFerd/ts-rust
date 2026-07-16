//! Exact source integration for one required own `identifier.name` access.
//!
//! The receiver must already have a canonical `any` type or belong to the
//! validated own-property object domain in `relater`. Optional properties,
//! missing/apparent/index members, and chains stay fail-closed. A member call
//! is admitted only when its exact enclosing call grants callee capability.

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::SemanticSymbolId;

use super::{
    CanonicalTypeMapperStore, RelationUnavailable, SymbolNodeLinks, TypeId, TypeNodeLinks,
    source::{PlannedExpression, PlannedExpressionKind},
};

/// A source property form outside the dependency-closed read slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourcePropertyUnsupported {
    Access(NodeRef),
    Receiver(NodeRef),
    MemberCall(NodeRef),
    MissingOwnProperty {
        node: NodeRef,
        receiver_type: TypeId,
    },
    OptionalProperty {
        node: NodeRef,
        property: SemanticSymbolId,
    },
}

/// Exact property planning/execution failure without a fallback result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourcePropertyError {
    Unsupported(SourcePropertyUnsupported),
    InvalidCache(NodeRef),
    Relation(RelationUnavailable),
}

impl From<RelationUnavailable> for SourcePropertyError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl std::fmt::Display for SourcePropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(error) => {
                write!(formatter, "source property is unsupported: {error:?}")
            }
            Self::InvalidCache(node) => {
                write!(formatter, "source property cache is invalid at {node:?}")
            }
            Self::Relation(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for SourcePropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::Unsupported(_) | Self::InvalidCache(_) => None,
        }
    }
}

/// Fully proven property syntax plus its source-planned receiver.
#[derive(Clone, Debug)]
pub(super) struct SourcePropertyPlan {
    pub(super) node: NodeRef,
    pub(super) receiver: PlannedExpression,
    name_node: NodeRef,
    name: String,
    position: SourcePropertyPosition,
}

/// The exact source position for which a property access was proven.
///
/// Retaining this capability in both syntax and finished plans prevents an
/// ordinary read plan from being repurposed as a member-call callee.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourcePropertyPosition {
    Read,
    CallCallee(NodeRef),
}

/// Property-access syntax proven before recursive source planning starts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectSourcePropertySyntax {
    node: NodeRef,
    receiver: NodeRef,
    name_node: NodeRef,
    name: String,
    position: SourcePropertyPosition,
}

impl DirectSourcePropertySyntax {
    pub(super) fn receiver(&self) -> NodeRef {
        self.receiver
    }

    pub(super) fn name_node(&self) -> NodeRef {
        self.name_node
    }
}

impl SourcePropertyPlan {
    pub(super) fn is_call_callee_for(&self, call: NodeRef, name: NodeRef) -> bool {
        self.name_node == name && self.position == SourcePropertyPosition::CallCallee(call)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceProperty {
    pub(super) type_: TypeId,
}

/// Proves the exact `identifier.name` syntax and all existing access-cache
/// shapes before source execution can publish semantic state.
pub(super) fn plan_direct_source_property_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    plan_direct_source_property_syntax_at(arena, store, node, SourcePropertyPosition::Read)
}

/// Proves a property access specifically as the callee of `call`.
pub(super) fn plan_direct_source_property_call_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    call: NodeRef,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    plan_direct_source_property_syntax_at(
        arena,
        store,
        node,
        SourcePropertyPosition::CallCallee(call),
    )
}

fn plan_direct_source_property_syntax_at(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    position: SourcePropertyPosition,
) -> Result<DirectSourcePropertySyntax, SourcePropertyError> {
    let Some(record) = arena.get(node.node) else {
        return Err(unsupported_access(node));
    };
    let NodeData::PropertyAccessExpression(access) = &record.data else {
        return Err(unsupported_access(node));
    };
    if record.kind != SyntaxKind::PropertyAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
    {
        return Err(unsupported_access(node));
    }

    match position {
        SourcePropertyPosition::Read => {
            if let Some(parent) = record.parent
                && let Some(parent_record) = arena.get(parent)
                && let NodeData::CallExpression(call) = &parent_record.data
                && call.expression == node.node
            {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MemberCall(NodeRef::new(
                        node.arena, node.file, parent,
                    )),
                ));
            }
        }
        SourcePropertyPosition::CallCallee(call_node) => {
            let exact_call = call_node.arena == node.arena
                && call_node.file == node.file
                && record.parent == Some(call_node.node)
                && arena.get(call_node.node).is_some_and(|call_record| {
                    call_record.kind == SyntaxKind::CallExpression
                        && matches!(
                            &call_record.data,
                            NodeData::CallExpression(call) if call.expression == node.node
                        )
                });
            if !exact_call {
                return Err(SourcePropertyError::Unsupported(
                    SourcePropertyUnsupported::MemberCall(call_node),
                ));
            }
        }
    }

    let receiver = NodeRef::new(node.arena, node.file, access.expression);
    let Some(receiver_record) = arena.get(access.expression) else {
        return Err(unsupported_access(node));
    };
    if receiver_record.parent != Some(node.node)
        || receiver_record.kind != SyntaxKind::Identifier
        || receiver_record.flags.0 != 0
        || !matches!(
            &receiver_record.data,
            NodeData::Identifier(identifier) if identifier.flow_node.is_none()
        )
    {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(receiver),
        ));
    }

    let name_node = NodeRef::new(node.arena, node.file, access.name);
    let Some(name_record) = arena.get(access.name) else {
        return Err(unsupported_access(node));
    };
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_access(node));
    };
    if name_record.parent != Some(node.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported_access(node));
    }

    preflight_property_links(store, node)?;
    Ok(DirectSourcePropertySyntax {
        node,
        receiver,
        name_node,
        name: identifier.text.clone(),
        position,
    })
}

pub(super) fn finish_direct_source_property_plan(
    syntax: &DirectSourcePropertySyntax,
    receiver: PlannedExpression,
) -> Result<SourcePropertyPlan, SourcePropertyError> {
    if receiver.node != syntax.receiver
        || !matches!(receiver.kind, PlannedExpressionKind::Identifier(_))
    {
        return Err(SourcePropertyError::Unsupported(
            SourcePropertyUnsupported::Receiver(syntax.receiver),
        ));
    }
    Ok(SourcePropertyPlan {
        node: syntax.node,
        receiver,
        name_node: syntax.name_node,
        name: syntax.name.clone(),
        position: syntax.position,
    })
}

/// Resolves an already-typed receiver and atomically publishes the access's
/// exact symbol/type cache pair. Canonical `any` publishes only its type cache.
pub(super) fn check_direct_source_property(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourcePropertyPlan,
    receiver_type: TypeId,
) -> Result<CheckedSourceProperty, SourcePropertyError> {
    debug_assert!(matches!(
        plan.receiver.kind,
        PlannedExpressionKind::Identifier(_)
    ));
    let any = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .any_type;
    let (type_, property) = if receiver_type == any {
        (any, None)
    } else {
        let Some(property) = store.resolved_own_property(receiver_type, &plan.name)? else {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MissingOwnProperty {
                    node: plan.node,
                    receiver_type,
                },
            ));
        };
        if property.optional {
            return Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::OptionalProperty {
                    node: plan.node,
                    property: property.symbol,
                },
            ));
        }
        (property.type_, Some(property.symbol))
    };

    publish_property_links(store, plan.node, property, type_)?;
    Ok(CheckedSourceProperty { type_ })
}

fn unsupported_access(node: NodeRef) -> SourcePropertyError {
    SourcePropertyError::Unsupported(SourcePropertyUnsupported::Access(node))
}

fn preflight_property_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourcePropertyError> {
    if let Some(links) = store.type_node_links(node) {
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(SourcePropertyError::InvalidCache(node));
        }
    }
    if let Some(links) = store.symbol_node_links(node)
        && links
            .resolved_symbol
            .is_some_and(|symbol| store.symbol(symbol).is_none())
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

fn publish_property_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    property: Option<SemanticSymbolId>,
    type_: TypeId,
) -> Result<(), SourcePropertyError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: property,
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_type)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    if property.is_some() && !store.set_symbol_node_links(node, expected_symbol) {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    if !store.set_type_node_links(node, expected_type) {
        return Err(SourcePropertyError::InvalidCache(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, ValueSymbolLinks,
        source::{PlannedIdentifierRead, PlannedIdentifierReadKind},
        types::ObjectFlags,
    };

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn registered_store(parsed: &ParseResult, file: FileId) -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn property_access(parsed: &ParseResult, file: FileId) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn identifier_receiver(
        syntax: &DirectSourcePropertySyntax,
        symbol: SemanticSymbolId,
    ) -> PlannedExpression {
        PlannedExpression::new(
            syntax.receiver(),
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
        )
    }

    fn property_object(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_: TypeId,
        optional: bool,
    ) -> (TypeId, SemanticSymbolId) {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let property = store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(name), property),
            Some(None)
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        (object, property)
    }

    #[test]
    fn required_own_property_publishes_exact_symbol_and_type_cold_and_warm() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(501);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (object, property) = property_object(&mut store, "value", string, false);
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan =
            finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, &plan, object),
            Ok(CheckedSourceProperty { type_: string })
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        assert_eq!(
            store
                .symbol_node_links(access)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
        assert_eq!(
            check_direct_source_property(&mut store, &plan, object),
            Ok(CheckedSourceProperty { type_: string })
        );
    }

    #[test]
    fn canonical_any_publishes_only_the_exact_type_cache() {
        let parsed = parsed("const result = value.name;");
        let file = FileId::new(502);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("value"),
            ))
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, &plan, any),
            Ok(CheckedSourceProperty { type_: any })
        );
        assert_eq!(
            store
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(any)
        );
        assert!(store.symbol_node_links(access).is_none());
    }

    #[test]
    fn missing_and_optional_properties_fail_before_cache_publication() {
        for (index, optional) in [false, true].into_iter().enumerate() {
            let parsed = parsed("const result = object.value;");
            let file = FileId::new(503 + u32::try_from(index).unwrap());
            let access = property_access(&parsed, file);
            let mut store = registered_store(&parsed, file);
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            let name = if optional { "value" } else { "other" };
            let (object, property) = property_object(&mut store, name, string, optional);
            let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
            let plan =
                finish_direct_source_property_plan(&syntax, identifier_receiver(&syntax, property))
                    .unwrap();

            let result = check_direct_source_property(&mut store, &plan, object);
            if optional {
                assert_eq!(
                    result,
                    Err(SourcePropertyError::Unsupported(
                        SourcePropertyUnsupported::OptionalProperty {
                            node: access,
                            property,
                        },
                    ))
                );
            } else {
                assert_eq!(
                    result,
                    Err(SourcePropertyError::Unsupported(
                        SourcePropertyUnsupported::MissingOwnProperty {
                            node: access,
                            receiver_type: object,
                        },
                    ))
                );
            }
            assert!(store.type_node_links(access).is_none());
            assert!(store.symbol_node_links(access).is_none());
        }
    }

    #[test]
    fn optional_chains_member_calls_and_poisoned_caches_fail_closed() {
        let optional = parsed("const result = object?.value;");
        let optional_file = FileId::new(505);
        let optional_access = property_access(&optional, optional_file);
        let optional_store = registered_store(&optional, optional_file);
        assert_eq!(
            plan_direct_source_property_syntax(&optional.arena, &optional_store, optional_access,),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::Access(optional_access),
            ))
        );

        let call = parsed("const result = object.value();");
        let call_file = FileId::new(506);
        let call_access = property_access(&call, call_file);
        let call_store = registered_store(&call, call_file);
        assert!(matches!(
            plan_direct_source_property_syntax(&call.arena, &call_store, call_access),
            Err(SourcePropertyError::Unsupported(
                SourcePropertyUnsupported::MemberCall(_)
            ))
        ));

        let poisoned = parsed("const result = object.value;");
        let poisoned_file = FileId::new(507);
        let poisoned_access = property_access(&poisoned, poisoned_file);
        let mut poisoned_store = registered_store(&poisoned, poisoned_file);
        assert!(poisoned_store.set_type_node_links(
            poisoned_access,
            TypeNodeLinks {
                outer_type_parameters: Some(Vec::new()),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            plan_direct_source_property_syntax(&poisoned.arena, &poisoned_store, poisoned_access,),
            Err(SourcePropertyError::InvalidCache(poisoned_access))
        );
    }

    #[test]
    fn union_receivers_fail_before_cache_publication() {
        let parsed = parsed("const result = object.value;");
        let file = FileId::new(508);
        let access = property_access(&parsed, file);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let union = store.literal_union_type(&[string, number], None).unwrap();
        let receiver_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("object"),
            ))
            .unwrap();
        let syntax = plan_direct_source_property_syntax(&parsed.arena, &store, access).unwrap();
        let plan = finish_direct_source_property_plan(
            &syntax,
            identifier_receiver(&syntax, receiver_symbol),
        )
        .unwrap();

        assert_eq!(
            check_direct_source_property(&mut store, &plan, union),
            Err(SourcePropertyError::Relation(
                RelationUnavailable::UnsupportedStructuredType(union),
            ))
        );
        assert!(store.type_node_links(access).is_none());
        assert!(store.symbol_node_links(access).is_none());
    }
}
