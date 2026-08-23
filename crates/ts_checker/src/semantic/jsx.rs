//! Canonical checking for basic JSX elements.
//!
//! This module follows the pinned JSX checker for global `JSX` namespaces,
//! named or indexed intrinsic tags, and fixed function components. It writes
//! only to the existing semantic graph. Inline object-literal spreads reuse
//! canonical object publication. Other spreads, generic components, dotted
//! component names, contextual children, and factory imports remain explicit
//! source-capability boundaries.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags,
};
use ts_core::TextRange;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::Number;

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalCheckerRelatedInformation, CanonicalTypeMapperStore,
    DeclaredTypeHost, DeclaredTypeLinks, JsxElementLinks, JsxFlags, ResolvedSignatureState,
    SignatureId, SignatureLinks, SourceCheckError, SourceCheckProvenanceError,
    SourceLiteralCacheError, SourceSyntaxRole, SymbolNodeLinks, TypeId, TypeNodeLinks,
    UnsupportedSourceSyntax, ValueSymbolLinks,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    formatter::{
        CanonicalTypeFormatFlags, get_type_names_for_assignability_error,
        type_to_string_with_host_and_flags,
    },
    indexed_access_types::template_pattern_index_matches_name,
    production::{CanonicalJsxRuntime, CanonicalJsxRuntimeEvidence},
    signatures::SignatureFlags,
    source::merge_retry_diagnostic,
    spelling::get_spelling_suggestion,
    type_nodes::CanonicalTypeQuery,
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Debug)]
struct JsxElementPlan {
    expression: NodeRef,
    opening: NodeRef,
    kind: JsxElementPlanKind,
    children: Vec<JsxChildPlan>,
}

#[derive(Clone, Debug)]
enum JsxElementPlanKind {
    Element {
        tag: JsxTagPlan,
        attributes_node: NodeRef,
        attributes: JsxAttributesPlan,
        type_arguments: Vec<NodeRef>,
        closing: Option<JsxClosingPlan>,
    },
    Fragment,
}

#[derive(Clone, Debug)]
struct JsxTagPlan {
    node: NodeRef,
    name: String,
    intrinsic: bool,
}

#[derive(Clone, Debug)]
struct JsxClosingPlan {
    node: NodeRef,
    tag: JsxTagPlan,
}

#[derive(Clone, Debug)]
struct JsxAttributePlan {
    node: NodeRef,
    name_node: NodeRef,
    name: String,
    symbol: SemanticSymbolId,
    value: JsxAttributeValue,
}

#[derive(Clone, Debug)]
enum JsxAttributesPlan {
    Properties(Vec<JsxAttributePlan>),
    ObjectSpread(Box<JsxObjectSpreadPlan>),
}

#[derive(Clone, Debug)]
struct JsxObjectSpreadPlan {
    node: NodeRef,
    object: super::object_members::PropertyObjectPlan,
    properties: Vec<JsxAttributePlan>,
}

#[derive(Clone, Debug)]
enum JsxAttributeValue {
    ImplicitTrue,
    Expression {
        wrapper: Option<NodeRef>,
        value: JsxScalarPlan,
    },
}

#[derive(Clone, Debug)]
enum JsxScalarPlan {
    String {
        node: NodeRef,
        value: String,
    },
    Number {
        node: NodeRef,
        value: Number,
    },
    Boolean {
        node: NodeRef,
        value: bool,
    },
    Null(NodeRef),
    Identifier {
        node: NodeRef,
        name: String,
    },
    Property {
        node: NodeRef,
        receiver: Box<Self>,
        name_node: NodeRef,
        name: String,
    },
    AnyAssertion {
        node: NodeRef,
        type_node: NodeRef,
        value: Box<Self>,
    },
    Parenthesized {
        node: NodeRef,
        value: Box<Self>,
    },
    Conditional {
        node: NodeRef,
        condition: Box<Self>,
        when_true: Box<Self>,
        when_false: Box<Self>,
    },
    Element(Box<JsxElementPlan>),
}

#[derive(Clone, Debug)]
enum JsxChildPlan {
    Text {
        node: NodeRef,
    },
    Expression {
        wrapper: NodeRef,
        value: JsxScalarPlan,
    },
    Element(Box<JsxElementPlan>),
}

#[derive(Clone, Copy, Debug)]
struct JsxNamespace {
    element_type: TypeId,
    intrinsic_elements: Option<TypeId>,
    unknown_symbol: SemanticSymbolId,
    error_type: TypeId,
    any_type: TypeId,
}

#[derive(Clone, Copy, Debug)]
struct JsxIntrinsicResolution {
    symbol: SemanticSymbolId,
    attributes_type: TypeId,
    flags: JsxFlags,
}

#[derive(Clone, Debug)]
struct CheckedJsxAttribute {
    plan: JsxAttributePlan,
    type_: TypeId,
}

#[derive(Clone, Copy, Debug)]
struct CheckedJsxChildren {
    node: NodeRef,
    type_: TypeId,
}

#[derive(Clone, Copy, Debug)]
struct JsxNamespaceProperty {
    symbol: SemanticSymbolId,
    type_: TypeId,
}

#[derive(Clone, Copy, Debug)]
struct JsxNamespaceIndex {
    declaration: NodeRef,
    key_type: TypeId,
    value_type: TypeId,
}

impl CanonicalTypeMapperStore {
    /// Validates a JSX expression and every supported child without mutation.
    ///
    /// Source planners can call this before executing earlier statements. It
    /// rejects unsupported tags, spread forms, malformed binder ownership, and
    /// unsupported scalar expressions across the complete JSX tree.
    ///
    /// # Errors
    ///
    /// Returns [`SourceCheckError`] when the host, syntax tree, or declaration
    /// graph cannot prove the complete JSX expression.
    pub fn preflight_jsx_element(
        &self,
        host: &DeclaredTypeHost<'_>,
        expression: NodeRef,
    ) -> Result<(), SourceCheckError> {
        let (arena, bound) = host.source(expression).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingNode(expression),
        ))?;
        if !self.contains_node_ref(expression) || !bound.contains(expression) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::NodeNotBound(expression),
            ));
        }
        plan_jsx_element(arena, bound, self, expression).map(|_| ())
    }

    /// Checks one parsed JSX element through the canonical semantic graph.
    ///
    /// The host must own the element's complete AST and binder data. Global
    /// `JSX.Element` uses existing declaration queries. `JSX.IntrinsicElements`
    /// is resolved only when the planned tree contains an intrinsic tag.
    /// Intrinsic tags retain their upstream symbol, signature, attribute, and
    /// JSX links. Function components reuse their existing fixed call signature.
    /// Unsupported syntax returns a typed source boundary instead of inventing
    /// an `any` result.
    ///
    /// # Errors
    ///
    /// Returns [`SourceCheckError`] when source identity, namespace types,
    /// component signatures, scalar expressions, relation state, or existing
    /// semantic links cannot be validated.
    pub fn check_jsx_element(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        expression: NodeRef,
        options: CanonicalCheckerOptions,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, SourceCheckError> {
        let (arena, bound) = host.source(expression).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingNode(expression),
        ))?;
        if !self.contains_node_ref(expression) || !bound.contains(expression) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::NodeNotBound(expression),
            ));
        }

        let plan = plan_jsx_element(arena, bound, self, expression)?;
        let namespace = resolve_jsx_namespace(self, host, options, diagnostics, &plan)?;
        execute_jsx_element(self, arena, bound, &namespace, &plan, options, diagnostics)
    }
}

pub(super) fn source_jsx_runtime_diagnostics(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    runtime: CanonicalJsxRuntimeEvidence<'_>,
) -> Result<CanonicalCheckerDiagnostics, SourceCheckError> {
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    match runtime {
        CanonicalJsxRuntimeEvidence::Preserve => {}
        CanonicalJsxRuntimeEvidence::Classic {
            factory_namespace,
            fragment_factory_namespace,
            fragment_factory_required,
            fragment_factory_pragma_required,
        } => {
            if factory_namespace.is_empty() || fragment_factory_namespace.is_empty() {
                return Err(unsupported(bound.source_file(), SyntaxKind::SourceFile));
            }
            let mut openings = arena
                .iter()
                .filter_map(|(node, record)| {
                    let (location, fragment) = match &record.data {
                        NodeData::JsxOpeningElement(element)
                            if record.kind == SyntaxKind::JsxOpeningElement =>
                        {
                            (element.tag_name, None)
                        }
                        NodeData::JsxSelfClosingElement(element)
                            if record.kind == SyntaxKind::JsxSelfClosingElement =>
                        {
                            (element.tag_name, None)
                        }
                        NodeData::JsxFragment(fragment)
                            if record.kind == SyntaxKind::JsxFragment =>
                        {
                            (fragment.opening_fragment, Some(node))
                        }
                        _ => return None,
                    };
                    Some((
                        record.range.start,
                        NodeRef::new(arena.id(), bound.file_id(), location),
                        fragment
                            .map(|fragment| NodeRef::new(arena.id(), bound.file_id(), fragment)),
                    ))
                })
                .collect::<Vec<_>>();
            openings.sort_by_key(|(position, _, _)| *position);

            let mut fragment_factory_checked = false;
            for (_, location, fragment) in openings {
                let Some(fragment) = fragment else {
                    if !jsx_factory_is_in_scope_at(store, arena, bound, location, factory_namespace)
                    {
                        add_diagnostic(&mut diagnostics, location, 2874, [factory_namespace])?;
                    }
                    continue;
                };

                let missing_fragment_factory = fragment_factory_namespace != "null"
                    && !jsx_factory_is_in_scope_at(
                        store,
                        arena,
                        bound,
                        location,
                        fragment_factory_namespace,
                    );
                if missing_fragment_factory {
                    add_diagnostic(
                        &mut diagnostics,
                        location,
                        2874,
                        [fragment_factory_namespace],
                    )?;
                }
                if factory_namespace != fragment_factory_namespace
                    && !jsx_factory_is_in_scope_at(store, arena, bound, location, factory_namespace)
                {
                    add_diagnostic(&mut diagnostics, location, 2874, [factory_namespace])?;
                }
                if !fragment_factory_checked && missing_fragment_factory {
                    add_diagnostic(
                        &mut diagnostics,
                        location,
                        2879,
                        [fragment_factory_namespace],
                    )?;
                }
                fragment_factory_checked = true;

                if fragment_factory_required || fragment_factory_pragma_required {
                    add_diagnostic(
                        &mut diagnostics,
                        fragment,
                        if fragment_factory_required {
                            17_016
                        } else {
                            17_017
                        },
                        std::iter::empty::<&str>(),
                    )?;
                }
            }
        }
        CanonicalJsxRuntimeEvidence::Automatic {
            module_specifier,
            resolved_module,
        } => {
            if module_specifier.is_empty() {
                return Err(unsupported(bound.source_file(), SyntaxKind::SourceFile));
            }
            if let Some(module) = resolved_module {
                let record = store
                    .symbol(module)
                    .ok_or(SourceCheckError::Import(bound.source_file()))?;
                if !record.flags().intersects(SymbolFlags::MODULE) {
                    return Err(SourceCheckError::Import(bound.source_file()));
                }
            } else if let Some((_, expression)) = arena
                .iter()
                .filter_map(|(node, record)| {
                    let location = match &record.data {
                        NodeData::JsxElement(_) if record.kind == SyntaxKind::JsxElement => node,
                        NodeData::JsxSelfClosingElement(_)
                            if record.kind == SyntaxKind::JsxSelfClosingElement =>
                        {
                            node
                        }
                        NodeData::JsxFragment(fragment)
                            if record.kind == SyntaxKind::JsxFragment =>
                        {
                            fragment.opening_fragment
                        }
                        _ => return None,
                    };
                    Some((
                        record.range.start,
                        NodeRef::new(arena.id(), bound.file_id(), location),
                    ))
                })
                .min_by_key(|(position, _)| *position)
            {
                add_diagnostic(&mut diagnostics, expression, 2875, [module_specifier])?;
            }
        }
    }
    Ok(diagnostics)
}

fn jsx_factory_is_in_scope_at(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    location: NodeRef,
    namespace: &str,
) -> bool {
    let mut current = Some(location);
    while let Some(node) = current {
        if bound
            .locals(node)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(namespace))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|symbol| {
                symbol
                    .flags()
                    .intersects(SymbolFlags::VALUE | SymbolFlags::ALIAS)
            })
        {
            return true;
        }
        current = arena
            .get(node.node)
            .and_then(|record| record.parent)
            .map(|parent| NodeRef::new(node.arena, node.file, parent));
    }
    store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(namespace))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|symbol| {
            symbol
                .flags()
                .intersects(SymbolFlags::VALUE | SymbolFlags::ALIAS)
        })
}

#[allow(clippy::too_many_lines)] // Keep the three parser-owned JSX node forms together.
fn plan_jsx_element(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    expression: NodeRef,
) -> Result<JsxElementPlan, SourceCheckError> {
    let record = jsx_node(arena, bound, store, expression)?;
    if record.flags.0 != 0 {
        return Err(unsupported(expression, record.kind));
    }
    match &record.data {
        NodeData::JsxSelfClosingElement(element)
            if record.kind == SyntaxKind::JsxSelfClosingElement && element.facts == 0 =>
        {
            let opening = expression;
            let tag = plan_jsx_tag(arena, bound, store, opening, element.tag_name)?;
            let attributes_node = child_ref(opening, element.attributes);
            let attributes = plan_jsx_attributes(arena, bound, store, opening, attributes_node)?;
            let type_arguments = plan_type_arguments(
                arena,
                bound,
                store,
                opening,
                element.type_arguments.as_ref(),
            )?;
            Ok(JsxElementPlan {
                expression,
                opening,
                kind: JsxElementPlanKind::Element {
                    tag,
                    attributes_node,
                    attributes,
                    type_arguments,
                    closing: None,
                },
                children: Vec::new(),
            })
        }
        NodeData::JsxElement(element)
            if record.kind == SyntaxKind::JsxElement && element.facts == 0 =>
        {
            let opening = child_ref(expression, element.opening_element);
            let opening_record = jsx_node(arena, bound, store, opening)?;
            let NodeData::JsxOpeningElement(opening_data) = &opening_record.data else {
                return Err(unsupported(opening, opening_record.kind));
            };
            if opening_record.kind != SyntaxKind::JsxOpeningElement
                || opening_record.flags.0 != 0
                || opening_record.parent != Some(expression.node)
                || opening_data.facts != 0
            {
                return Err(unsupported(opening, opening_record.kind));
            }
            let tag = plan_jsx_tag(arena, bound, store, opening, opening_data.tag_name)?;
            let attributes_node = child_ref(opening, opening_data.attributes);
            let attributes = plan_jsx_attributes(arena, bound, store, opening, attributes_node)?;
            let type_arguments = plan_type_arguments(
                arena,
                bound,
                store,
                opening,
                opening_data.type_arguments.as_ref(),
            )?;

            let closing_node = child_ref(expression, element.closing_element);
            let closing_record = jsx_node(arena, bound, store, closing_node)?;
            let NodeData::JsxClosingElement(closing_data) = &closing_record.data else {
                return Err(unsupported(closing_node, closing_record.kind));
            };
            if closing_record.kind != SyntaxKind::JsxClosingElement
                || closing_record.parent != Some(expression.node)
            {
                return Err(unsupported(closing_node, closing_record.kind));
            }
            let closing_tag =
                plan_jsx_tag(arena, bound, store, closing_node, closing_data.tag_name)?;
            Ok(JsxElementPlan {
                expression,
                opening,
                kind: JsxElementPlanKind::Element {
                    tag,
                    attributes_node,
                    attributes,
                    type_arguments,
                    closing: Some(JsxClosingPlan {
                        node: closing_node,
                        tag: closing_tag,
                    }),
                },
                children: plan_jsx_children(
                    arena,
                    bound,
                    store,
                    expression,
                    &element.children.nodes,
                )?,
            })
        }
        NodeData::JsxFragment(fragment)
            if record.kind == SyntaxKind::JsxFragment && fragment.facts == 0 =>
        {
            let opening = child_ref(expression, fragment.opening_fragment);
            let closing = child_ref(expression, fragment.closing_fragment);
            let opening_record = jsx_node(arena, bound, store, opening)?;
            let closing_record = jsx_node(arena, bound, store, closing)?;
            if opening_record.kind != SyntaxKind::JsxOpeningFragment
                || !matches!(&opening_record.data, NodeData::JsxOpeningFragment(_))
                || opening_record.parent != Some(expression.node)
                || closing_record.kind != SyntaxKind::JsxClosingFragment
                || !matches!(&closing_record.data, NodeData::JsxClosingFragment(_))
                || closing_record.parent != Some(expression.node)
            {
                return Err(unsupported(expression, record.kind));
            }
            Ok(JsxElementPlan {
                expression,
                opening,
                kind: JsxElementPlanKind::Fragment,
                children: plan_jsx_children(
                    arena,
                    bound,
                    store,
                    expression,
                    &fragment.children.nodes,
                )?,
            })
        }
        _ => Err(unsupported(expression, record.kind)),
    }
}

fn plan_jsx_tag(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    parent: NodeRef,
    tag: ts_ast::NodeId,
) -> Result<JsxTagPlan, SourceCheckError> {
    let node = child_ref(parent, tag);
    let record = jsx_node(arena, bound, store, node)?;
    if record.parent != Some(parent.node) || record.flags.0 != 0 {
        return Err(unsupported(node, record.kind));
    }
    match &record.data {
        NodeData::Identifier(identifier) if record.kind == SyntaxKind::Identifier => {
            if identifier.flow_node.is_some() || identifier.text.is_empty() {
                return Err(unsupported(node, record.kind));
            }
            Ok(JsxTagPlan {
                node,
                name: identifier.text.clone(),
                intrinsic: is_intrinsic_name(&identifier.text),
            })
        }
        NodeData::JsxNamespacedName(namespaced)
            if record.kind == SyntaxKind::JsxNamespacedName && namespaced.facts == 0 =>
        {
            let namespace = child_ref(node, namespaced.namespace);
            let name = child_ref(node, namespaced.name);
            let namespace_record = jsx_node(arena, bound, store, namespace)?;
            let name_record = jsx_node(arena, bound, store, name)?;
            let (NodeData::Identifier(namespace_name), NodeData::Identifier(local_name)) =
                (&namespace_record.data, &name_record.data)
            else {
                return Err(unsupported(node, record.kind));
            };
            if namespace_record.parent != Some(node.node)
                || name_record.parent != Some(node.node)
                || namespace_name.text.is_empty()
                || local_name.text.is_empty()
            {
                return Err(unsupported(node, record.kind));
            }
            Ok(JsxTagPlan {
                node,
                name: format!("{}:{}", namespace_name.text, local_name.text),
                intrinsic: true,
            })
        }
        _ => Err(unsupported(node, record.kind)),
    }
}

fn plan_type_arguments(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    opening: NodeRef,
    arguments: Option<&ts_ast::NodeList>,
) -> Result<Vec<NodeRef>, SourceCheckError> {
    arguments.map_or_else(
        || Ok(Vec::new()),
        |arguments| {
            if arguments.has_trailing_comma {
                return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
            }
            arguments
                .nodes
                .iter()
                .map(|argument| {
                    let argument = child_ref(opening, *argument);
                    let record = jsx_node(arena, bound, store, argument)?;
                    if record.parent != Some(opening.node) {
                        return Err(unsupported(argument, record.kind));
                    }
                    Ok(argument)
                })
                .collect()
        },
    )
}

fn plan_jsx_attributes(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    opening: NodeRef,
    attributes_node: NodeRef,
) -> Result<JsxAttributesPlan, SourceCheckError> {
    let attributes_record = jsx_node(arena, bound, store, attributes_node)?;
    let NodeData::JsxAttributes(attributes) = &attributes_record.data else {
        return Err(unsupported(attributes_node, attributes_record.kind));
    };
    if attributes_record.kind != SyntaxKind::JsxAttributes
        || attributes_record.parent != Some(opening.node)
        || attributes_record.flags.0 != 0
        || attributes.facts != 0
        || bound.symbol(attributes_node).is_none()
    {
        return Err(unsupported(attributes_node, attributes_record.kind));
    }

    if let [attribute] = attributes.properties.nodes.as_slice() {
        let node = child_ref(attributes_node, *attribute);
        let record = jsx_node(arena, bound, store, node)?;
        if matches!(&record.data, NodeData::JsxSpreadAttribute(_)) {
            return plan_jsx_object_spread(arena, bound, store, attributes_node, node)
                .map(|spread| JsxAttributesPlan::ObjectSpread(Box::new(spread)));
        }
    }

    attributes
        .properties
        .nodes
        .iter()
        .map(|attribute| {
            let node = child_ref(attributes_node, *attribute);
            let record = jsx_node(arena, bound, store, node)?;
            let NodeData::JsxAttribute(attribute) = &record.data else {
                return Err(unsupported(node, record.kind));
            };
            if record.kind != SyntaxKind::JsxAttribute
                || record.parent != Some(attributes_node.node)
                || record.flags.0 != 0
                || attribute.facts != 0
            {
                return Err(unsupported(node, record.kind));
            }
            let name_node = child_ref(node, attribute.name);
            let name_record = jsx_node(arena, bound, store, name_node)?;
            if name_record.parent != Some(node.node) {
                return Err(unsupported(name_node, name_record.kind));
            }
            let name = match &name_record.data {
                NodeData::Identifier(name)
                    if name_record.kind == SyntaxKind::Identifier && !name.text.is_empty() =>
                {
                    name.text.clone()
                }
                NodeData::JsxNamespacedName(namespaced)
                    if name_record.kind == SyntaxKind::JsxNamespacedName
                        && namespaced.facts == 0 =>
                {
                    let namespace = child_ref(name_node, namespaced.namespace);
                    let local = child_ref(name_node, namespaced.name);
                    let namespace_record = jsx_node(arena, bound, store, namespace)?;
                    let local_record = jsx_node(arena, bound, store, local)?;
                    let (NodeData::Identifier(namespace), NodeData::Identifier(local)) =
                        (&namespace_record.data, &local_record.data)
                    else {
                        return Err(unsupported(name_node, name_record.kind));
                    };
                    if namespace_record.kind != SyntaxKind::Identifier
                        || local_record.kind != SyntaxKind::Identifier
                        || namespace_record.parent != Some(name_node.node)
                        || local_record.parent != Some(name_node.node)
                        || namespace.text.is_empty()
                        || local.text.is_empty()
                    {
                        return Err(unsupported(name_node, name_record.kind));
                    }
                    format!("{}:{}", namespace.text, local.text)
                }
                _ => return Err(unsupported(name_node, name_record.kind)),
            };
            let symbol = bound.symbol(node).ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            ))?;
            let symbol_record = store
                .symbol(symbol)
                .ok_or(SourceCheckError::Property(node))?;
            if !symbol_record.flags().contains(SymbolFlags::PROPERTY)
                || symbol_record.name().as_utf8() != Some(name.as_str())
            {
                return Err(SourceCheckError::Property(node));
            }
            let value = match attribute.initializer {
                None => JsxAttributeValue::ImplicitTrue,
                Some(initializer) => {
                    let initializer = child_ref(node, initializer);
                    let initializer_record = jsx_node(arena, bound, store, initializer)?;
                    if initializer_record.parent != Some(node.node) {
                        return Err(unsupported(initializer, initializer_record.kind));
                    }
                    if let NodeData::JsxExpression(expression) = &initializer_record.data {
                        if initializer_record.kind != SyntaxKind::JsxExpression
                            || expression.dot_dot_dot_token.is_some()
                        {
                            return Err(unsupported(initializer, initializer_record.kind));
                        }
                        let inner = expression
                            .expression
                            .ok_or_else(|| unsupported(initializer, SyntaxKind::JsxExpression))?;
                        JsxAttributeValue::Expression {
                            wrapper: Some(initializer),
                            value: plan_scalar(
                                arena,
                                bound,
                                store,
                                initializer,
                                child_ref(initializer, inner),
                            )?,
                        }
                    } else {
                        JsxAttributeValue::Expression {
                            wrapper: None,
                            value: plan_scalar(arena, bound, store, node, initializer)?,
                        }
                    }
                }
            };
            Ok(JsxAttributePlan {
                node,
                name_node,
                name,
                symbol,
                value,
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(JsxAttributesPlan::Properties)
}

fn plan_jsx_object_spread(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    attributes: NodeRef,
    node: NodeRef,
) -> Result<JsxObjectSpreadPlan, SourceCheckError> {
    let record = jsx_node(arena, bound, store, node)?;
    let NodeData::JsxSpreadAttribute(spread) = &record.data else {
        return Err(unsupported(node, record.kind));
    };
    if record.kind != SyntaxKind::JsxSpreadAttribute
        || record.parent != Some(attributes.node)
        || record.flags.0 != 0
    {
        return Err(unsupported(node, record.kind));
    }

    let object_node = child_ref(node, spread.expression);
    let object_record = jsx_node(arena, bound, store, object_node)?;
    if object_record.kind != SyntaxKind::ObjectLiteralExpression
        || !matches!(&object_record.data, NodeData::ObjectLiteralExpression(_))
        || object_record.parent != Some(node.node)
    {
        return Err(unsupported(node, SyntaxKind::JsxSpreadAttribute));
    }

    let host = DeclaredTypeHost::new([(arena, bound)]).map_err(super::DeclaredTypeError::from)?;
    let object =
        super::object_members::plan_object_literal(store, &host, object_node).map_err(|error| {
            match error {
                super::object_members::PropertyObjectError::UnsupportedMember { node, kind } => {
                    unsupported(node, kind)
                }
                _ => SourceCheckError::Property(object_node),
            }
        })?;
    super::object_members::object_literal_state(store, &object)
        .map_err(|_| SourceCheckError::Property(object_node))?;

    let mut properties = Vec::with_capacity(object.properties.len());
    for property in &object.properties {
        let property_record = jsx_node(arena, bound, store, property.declaration)?;
        if property_record.kind != SyntaxKind::PropertyAssignment
            || !matches!(&property_record.data, NodeData::PropertyAssignment(_))
        {
            return Err(unsupported(property.declaration, property_record.kind));
        }
        let name_record = jsx_node(arena, bound, store, property.name_node)?;
        if name_record.kind != SyntaxKind::Identifier
            || !matches!(&name_record.data, NodeData::Identifier(_))
            || name_record.parent != Some(property.declaration.node)
        {
            return Err(unsupported(property.name_node, name_record.kind));
        }
        properties.push(JsxAttributePlan {
            node: property.declaration,
            name_node: property.name_node,
            name: property.name.clone(),
            symbol: property.symbol,
            value: JsxAttributeValue::Expression {
                wrapper: None,
                value: plan_scalar(
                    arena,
                    bound,
                    store,
                    property.declaration,
                    property.type_node,
                )?,
            },
        });
    }

    Ok(JsxObjectSpreadPlan {
        node,
        object,
        properties,
    })
}

fn plan_jsx_children(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    parent: NodeRef,
    children: &[ts_ast::NodeId],
) -> Result<Vec<JsxChildPlan>, SourceCheckError> {
    let mut result = Vec::with_capacity(children.len());
    for child in children {
        let child = child_ref(parent, *child);
        let record = jsx_node(arena, bound, store, child)?;
        if record.parent != Some(parent.node) {
            return Err(unsupported(child, record.kind));
        }
        match &record.data {
            NodeData::JsxText(text)
                if matches!(
                    record.kind,
                    SyntaxKind::JsxText | SyntaxKind::JsxTextAllWhiteSpaces
                ) =>
            {
                if !text.contains_only_trivia_white_spaces {
                    result.push(JsxChildPlan::Text { node: child });
                }
            }
            NodeData::JsxExpression(expression)
                if record.kind == SyntaxKind::JsxExpression
                    && expression.dot_dot_dot_token.is_none() =>
            {
                if let Some(value) = expression.expression {
                    result.push(JsxChildPlan::Expression {
                        wrapper: child,
                        value: plan_scalar(arena, bound, store, child, child_ref(child, value))?,
                    });
                }
            }
            NodeData::JsxElement(_)
            | NodeData::JsxSelfClosingElement(_)
            | NodeData::JsxFragment(_) => {
                result.push(JsxChildPlan::Element(Box::new(plan_jsx_element(
                    arena, bound, store, child,
                )?)));
            }
            _ => return Err(unsupported(child, record.kind)),
        }
    }
    Ok(result)
}

fn plan_scalar(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    parent: NodeRef,
    node: NodeRef,
) -> Result<JsxScalarPlan, SourceCheckError> {
    let record = jsx_node(arena, bound, store, node)?;
    if record.parent != Some(parent.node) || record.flags.0 != 0 {
        return Err(unsupported(node, record.kind));
    }
    match &record.data {
        NodeData::StringLiteral(literal)
            if record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
        {
            Ok(JsxScalarPlan::String {
                node,
                value: literal.text.clone(),
            })
        }
        NodeData::NumericLiteral(literal)
            if record.kind == SyntaxKind::NumericLiteral && literal.token_flags.0 == 0 =>
        {
            let value = ts_jsnum::from_string(&literal.text);
            if value.is_nan() {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::InvalidLiteralSpelling(node),
                ));
            }
            Ok(JsxScalarPlan::Number { node, value })
        }
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::TrueKeyword => {
            Ok(JsxScalarPlan::Boolean { node, value: true })
        }
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::FalseKeyword => {
            Ok(JsxScalarPlan::Boolean { node, value: false })
        }
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::NullKeyword => {
            Ok(JsxScalarPlan::Null(node))
        }
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
        {
            Ok(JsxScalarPlan::Identifier {
                node,
                name: identifier.text.clone(),
            })
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.question_dot_token.is_none()
                && access.flow_node.is_none()
                && access.facts == 0 =>
        {
            let receiver_node = child_ref(node, access.expression);
            let receiver_record = jsx_node(arena, bound, store, receiver_node)?;
            if receiver_record.kind != SyntaxKind::Identifier
                || !matches!(&receiver_record.data, NodeData::Identifier(_))
            {
                return Err(unsupported(receiver_node, receiver_record.kind));
            }
            let receiver = plan_scalar(arena, bound, store, node, receiver_node)?;
            let name_node = child_ref(node, access.name);
            let name_record = jsx_node(arena, bound, store, name_node)?;
            let NodeData::Identifier(name) = &name_record.data else {
                return Err(unsupported(name_node, name_record.kind));
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.parent != Some(node.node)
                || name_record.flags.0 != 0
                || name.flow_node.is_some()
                || name.text.is_empty()
            {
                return Err(unsupported(name_node, name_record.kind));
            }
            Ok(JsxScalarPlan::Property {
                node,
                receiver: Box::new(receiver),
                name_node,
                name: name.text.clone(),
            })
        }
        NodeData::AsExpression(assertion) if record.kind == SyntaxKind::AsExpression => {
            let type_node = child_ref(node, assertion.type_);
            let type_record = jsx_node(arena, bound, store, type_node)?;
            if type_record.kind != SyntaxKind::AnyKeyword
                || !matches!(&type_record.data, NodeData::KeywordTypeNode(_))
                || type_record.parent != Some(node.node)
            {
                return Err(unsupported(type_node, type_record.kind));
            }
            Ok(JsxScalarPlan::AnyAssertion {
                node,
                type_node,
                value: Box::new(plan_scalar(
                    arena,
                    bound,
                    store,
                    node,
                    child_ref(node, assertion.expression),
                )?),
            })
        }
        NodeData::ParenthesizedExpression(parenthesized)
            if record.kind == SyntaxKind::ParenthesizedExpression =>
        {
            let expression = child_ref(node, parenthesized.expression);
            Ok(JsxScalarPlan::Parenthesized {
                node,
                value: Box::new(plan_scalar(arena, bound, store, node, expression)?),
            })
        }
        NodeData::ConditionalExpression(conditional)
            if record.kind == SyntaxKind::ConditionalExpression && conditional.facts == 0 =>
        {
            let question = child_ref(node, conditional.question_token);
            let colon = child_ref(node, conditional.colon_token);
            let question_record = jsx_node(arena, bound, store, question)?;
            let colon_record = jsx_node(arena, bound, store, colon)?;
            if question_record.kind != SyntaxKind::QuestionToken
                || colon_record.kind != SyntaxKind::ColonToken
                || question_record.parent != Some(node.node)
                || colon_record.parent != Some(node.node)
            {
                return Err(unsupported(node, record.kind));
            }
            Ok(JsxScalarPlan::Conditional {
                node,
                condition: Box::new(plan_scalar(
                    arena,
                    bound,
                    store,
                    node,
                    child_ref(node, conditional.condition),
                )?),
                when_true: Box::new(plan_scalar(
                    arena,
                    bound,
                    store,
                    node,
                    child_ref(node, conditional.when_true),
                )?),
                when_false: Box::new(plan_scalar(
                    arena,
                    bound,
                    store,
                    node,
                    child_ref(node, conditional.when_false),
                )?),
            })
        }
        NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_) => {
            Ok(JsxScalarPlan::Element(Box::new(plan_jsx_element(
                arena, bound, store, node,
            )?)))
        }
        _ => Err(unsupported(node, record.kind)),
    }
}

fn resolve_jsx_namespace(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &JsxElementPlan,
) -> Result<JsxNamespace, SourceCheckError> {
    let location = plan.expression;
    let needs_intrinsics = jsx_plan_needs_intrinsic_elements(plan);
    let (globals, unknown_symbol, error_type, any_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        (
            bootstrap.globals,
            bootstrap.unknown_symbol,
            bootstrap.error_type,
            bootstrap.any_type,
        )
    };
    let namespace = store
        .symbol_table(globals)
        .ok_or(SourceCheckError::Property(location))?
        .get_source("JSX")
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .filter(|symbol| {
            store
                .symbol(*symbol)
                .is_some_and(|record| record.flags().intersects(SymbolFlags::NAMESPACE))
        });

    let mut element_type = error_type;
    let mut intrinsic_elements = None;
    if let Some(namespace) = namespace {
        let exports = store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .ok_or(SourceCheckError::Property(location))?;
        let table = store
            .symbol_table(exports)
            .ok_or(SourceCheckError::Property(location))?;
        let element = table.get_source("Element");
        let intrinsic = table.get_source("IntrinsicElements");
        if let Some(symbol) = element {
            if store
                .symbol(symbol)
                .is_none_or(|record| !record.flags().intersects(SymbolFlags::TYPE))
            {
                return Err(SourceCheckError::Property(location));
            }
            element_type = if !needs_intrinsics
                && matches!(&plan.kind, JsxElementPlanKind::Fragment)
                && jsx_namespace_interface_has_heritage(store, host, namespace, symbol)?
            {
                store.get_declared_type_of_symbol(host, symbol)?
            } else {
                resolve_namespace_export_type(store, host, namespace, symbol, options, diagnostics)?
            };
        }
        if let Some(symbol) = intrinsic {
            if store
                .symbol(symbol)
                .is_none_or(|record| !record.flags().intersects(SymbolFlags::TYPE))
            {
                return Err(SourceCheckError::Property(location));
            }
            if needs_intrinsics {
                intrinsic_elements = Some(resolve_namespace_export_type(
                    store,
                    host,
                    namespace,
                    symbol,
                    options,
                    diagnostics,
                )?);
            }
        }
    }

    Ok(JsxNamespace {
        element_type,
        intrinsic_elements,
        unknown_symbol,
        error_type,
        any_type,
    })
}

fn jsx_plan_needs_intrinsic_elements(plan: &JsxElementPlan) -> bool {
    let attributes_need_intrinsics = match &plan.kind {
        JsxElementPlanKind::Element {
            tag, attributes, ..
        } => {
            if tag.intrinsic {
                return true;
            }
            let properties = match attributes {
                JsxAttributesPlan::Properties(properties) => properties.as_slice(),
                JsxAttributesPlan::ObjectSpread(spread) => spread.properties.as_slice(),
            };
            properties.iter().any(|property| {
                matches!(
                    &property.value,
                    JsxAttributeValue::Expression { value, .. }
                        if jsx_scalar_needs_intrinsic_elements(value)
                )
            })
        }
        JsxElementPlanKind::Fragment => false,
    };
    attributes_need_intrinsics
        || plan.children.iter().any(|child| match child {
            JsxChildPlan::Text { .. } => false,
            JsxChildPlan::Expression { value, .. } => jsx_scalar_needs_intrinsic_elements(value),
            JsxChildPlan::Element(element) => jsx_plan_needs_intrinsic_elements(element),
        })
}

fn jsx_scalar_needs_intrinsic_elements(scalar: &JsxScalarPlan) -> bool {
    match scalar {
        JsxScalarPlan::Element(element) => jsx_plan_needs_intrinsic_elements(element),
        JsxScalarPlan::Property { receiver, .. } => jsx_scalar_needs_intrinsic_elements(receiver),
        JsxScalarPlan::AnyAssertion { value, .. } | JsxScalarPlan::Parenthesized { value, .. } => {
            jsx_scalar_needs_intrinsic_elements(value)
        }
        JsxScalarPlan::Conditional {
            condition,
            when_true,
            when_false,
            ..
        } => {
            jsx_scalar_needs_intrinsic_elements(condition)
                || jsx_scalar_needs_intrinsic_elements(when_true)
                || jsx_scalar_needs_intrinsic_elements(when_false)
        }
        JsxScalarPlan::String { .. }
        | JsxScalarPlan::Number { .. }
        | JsxScalarPlan::Boolean { .. }
        | JsxScalarPlan::Null(_)
        | JsxScalarPlan::Identifier { .. } => false,
    }
}

fn jsx_namespace_interface_has_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
) -> Result<bool, SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or_else(|| invalid_namespace_symbol(symbol))?;
    if record.flags() != SymbolFlags::INTERFACE || record.parent() != Some(namespace) {
        return Ok(false);
    }
    let declarations = record
        .declarations()
        .ok_or_else(|| invalid_namespace_symbol(symbol))?;
    for declaration in declarations {
        let node = host
            .node(*declaration)
            .ok_or(SourceCheckError::Property(*declaration))?;
        let NodeData::InterfaceDeclaration(interface) = &node.data else {
            return Err(SourceCheckError::Property(*declaration));
        };
        if node.kind != SyntaxKind::InterfaceDeclaration
            || !host.symbol_matches(store, *declaration, symbol)
        {
            return Err(SourceCheckError::Property(*declaration));
        }
        if interface.heritage_clauses.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}

fn resolve_namespace_export_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or(invalid_namespace_symbol(symbol))?;
    if record.flags() == SymbolFlags::INTERFACE && record.parent() == Some(namespace) {
        return resolve_namespace_interface(store, host, namespace, symbol, options, diagnostics);
    }
    CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_declared_type_of_symbol(symbol)
        .map_err(Into::into)
}

#[allow(clippy::too_many_lines)] // Namespace interface planning and publication share one proof.
fn resolve_namespace_interface(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let (declaration, members, member_nodes) = {
        let record = store
            .symbol(symbol)
            .ok_or_else(|| invalid_namespace_symbol(symbol))?;
        let [declaration] = record
            .declarations()
            .ok_or_else(|| invalid_namespace_symbol(symbol))?
        else {
            return Err(invalid_namespace_symbol(symbol));
        };
        let node = host
            .node(*declaration)
            .ok_or(SourceCheckError::Property(*declaration))?;
        let NodeData::InterfaceDeclaration(interface) = &node.data else {
            return Err(SourceCheckError::Property(*declaration));
        };
        if node.kind != SyntaxKind::InterfaceDeclaration
            || record.parent() != Some(namespace)
            || record.flags() != SymbolFlags::INTERFACE
            || record.check_flags() != CheckFlags::NONE
            || interface.type_parameters.is_some()
            || interface.heritage_clauses.is_some()
            || interface.members.has_trailing_comma
            || !host.symbol_matches(store, *declaration, symbol)
        {
            return Err(unsupported(*declaration, node.kind));
        }
        (
            *declaration,
            record.members(),
            interface.members.nodes.clone(),
        )
    };

    let mut properties = Vec::new();
    let mut indexes = Vec::new();
    for member_id in member_nodes {
        let member = child_ref(declaration, member_id);
        let record = host
            .node(member)
            .ok_or(SourceCheckError::Property(member))?;
        if record.parent != Some(declaration.node) {
            return Err(SourceCheckError::Property(member));
        }
        match &record.data {
            NodeData::PropertyDeclaration(property)
                if record.kind == SyntaxKind::PropertyDeclaration
                    && property.initializer.is_none()
                    && property.symbol.is_none()
                    && property.facts == 0 =>
            {
                let name_node = child_ref(member, property.name);
                let (name, computed_literal) =
                    jsx_namespace_property_name(host, member, name_node)?;
                let property_symbol = host
                    .bound_file(member)
                    .and_then(|bound| bound.symbol(member))
                    .ok_or(SourceCheckError::Provenance(
                        SourceCheckProvenanceError::MissingDeclarationSymbol(member),
                    ))?;
                let property_record = store
                    .symbol(property_symbol)
                    .ok_or(SourceCheckError::Property(member))?;
                if !property_record.flags().contains(SymbolFlags::PROPERTY)
                    || property_record.name().as_utf8() != Some(name.as_str())
                    || property_record.parent() != Some(symbol)
                    || members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get_source(&name))
                        != Some(property_symbol)
                {
                    return Err(SourceCheckError::Property(member));
                }
                let annotation = property
                    .type_
                    .map(|node| child_ref(member, node))
                    .ok_or_else(|| unsupported(member, record.kind))?;
                let type_ = CanonicalTypeQuery::new(store, host, options, diagnostics)?
                    .get_type_from_type_node(annotation)?;
                if let Some(literal) = computed_literal {
                    let record = host
                        .node(literal)
                        .ok_or(SourceCheckError::Property(literal))?;
                    let literal_type = match &record.data {
                        NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_) => {
                            store.regular_string_literal_type(name.clone())?
                        }
                        NodeData::NumericLiteral(_) => {
                            let value = ts_jsnum::from_string(&name);
                            if value.is_nan() {
                                return Err(SourceCheckError::Unsupported(
                                    UnsupportedSourceSyntax::InvalidLiteralSpelling(literal),
                                ));
                            }
                            store.regular_number_literal_type(value)?
                        }
                        _ => return Err(unsupported(literal, record.kind)),
                    };
                    publish_type_links(store, literal, literal_type)?;
                }
                properties.push(JsxNamespaceProperty {
                    symbol: property_symbol,
                    type_,
                });
            }
            NodeData::IndexSignatureDeclaration(index)
                if record.kind == SyntaxKind::IndexSignature
                    && index.type_parameters.is_none()
                    && index.parameters.nodes.len() == 1 =>
            {
                let parameter = child_ref(member, index.parameters.nodes[0]);
                let parameter_record = host
                    .node(parameter)
                    .ok_or(SourceCheckError::Property(parameter))?;
                let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
                    return Err(unsupported(parameter, parameter_record.kind));
                };
                let key = parameter_data
                    .type_
                    .map(|node| child_ref(parameter, node))
                    .ok_or_else(|| unsupported(parameter, parameter_record.kind))?;
                let value = child_ref(member, index.type_);
                let key_type = CanonicalTypeQuery::new(store, host, options, diagnostics)?
                    .get_type_from_type_node(key)?;
                let value_type = CanonicalTypeQuery::new(store, host, options, diagnostics)?
                    .get_type_from_type_node(value)?;
                indexes.push(JsxNamespaceIndex {
                    declaration: member,
                    key_type,
                    value_type,
                });
            }
            _ => return Err(unsupported(member, record.kind)),
        }
    }

    if let Some(type_) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    {
        validate_namespace_interface(
            store,
            type_,
            symbol,
            members,
            &properties,
            &indexes,
            declaration,
        )?;
        return Ok(type_);
    }

    if !store.try_reserve_types(1)
        || !store.try_reserve_declared_type_links(1)
        || !store.try_reserve_value_symbol_links(properties.len())
        || !store.try_reserve_index_infos(indexes.len())
    {
        return Err(SourceCheckError::Property(declaration));
    }
    for property in &properties {
        if store
            .value_symbol_links(property.symbol)
            .is_some_and(|links| {
                links != &ValueSymbolLinks::default()
                    && links
                        != &ValueSymbolLinks {
                            resolved_type: Some(property.type_),
                            ..ValueSymbolLinks::default()
                        }
            })
        {
            return Err(SourceCheckError::Property(declaration));
        }
    }

    let type_ = store
        .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
        .ok_or(SourceCheckError::Property(declaration))?;
    if !store.set_declared_type_links(
        symbol,
        DeclaredTypeLinks {
            declared_type: Some(type_),
            ..DeclaredTypeLinks::default()
        },
    ) || !store.set_interface_base_resolution(type_, true, None, None)
    {
        return Err(SourceCheckError::Property(declaration));
    }
    let mut index_infos = Vec::with_capacity(indexes.len());
    for index in indexes {
        index_infos.push(
            store
                .alloc_index_info(
                    index.key_type,
                    index.value_type,
                    false,
                    Some(index.declaration),
                    Vec::new(),
                )
                .ok_or(SourceCheckError::Property(index.declaration))?,
        );
    }
    for property in &properties {
        if !store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(property.type_),
                ..ValueSymbolLinks::default()
            },
        ) {
            return Err(SourceCheckError::Property(declaration));
        }
    }
    let property_symbols = (!properties.is_empty())
        .then(|| properties.iter().map(|property| property.symbol).collect());
    let index_infos = (!index_infos.is_empty()).then_some(index_infos);
    if !store.set_interface_declared_members(type_, true, members, None, None, index_infos.clone())
        || !store.set_structured_type_members(
            type_,
            members,
            property_symbols,
            None,
            None,
            index_infos,
        )
    {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(type_)
}

fn jsx_namespace_property_name(
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    name: NodeRef,
) -> Result<(String, Option<NodeRef>), SourceCheckError> {
    let record = host.node(name).ok_or(SourceCheckError::Property(name))?;
    if record.parent != Some(member.node) {
        return Err(SourceCheckError::Property(name));
    }
    match &record.data {
        NodeData::Identifier(identifier) if record.kind == SyntaxKind::Identifier => {
            Ok((identifier.text.clone(), None))
        }
        NodeData::StringLiteral(literal) if record.kind == SyntaxKind::StringLiteral => {
            Ok((literal.text.clone(), None))
        }
        NodeData::ComputedPropertyName(computed)
            if record.kind == SyntaxKind::ComputedPropertyName && computed.facts == 0 =>
        {
            let expression = child_ref(name, computed.expression);
            let literal_record = host
                .node(expression)
                .ok_or(SourceCheckError::Property(expression))?;
            if literal_record.parent != Some(name.node)
                || literal_record.flags.0 != 0
                || literal_record.range.start < record.range.start
                || literal_record.range.end > record.range.end
            {
                return Err(unsupported(name, record.kind));
            }
            let text = match &literal_record.data {
                NodeData::StringLiteral(literal)
                    if literal.token_flags.0 == 0
                        && literal_record.kind == SyntaxKind::StringLiteral =>
                {
                    literal.text.clone()
                }
                NodeData::NumericLiteral(literal)
                    if literal.token_flags.0 == 0
                        && literal_record.kind == SyntaxKind::NumericLiteral =>
                {
                    literal.text.clone()
                }
                NodeData::NoSubstitutionTemplateLiteral(literal)
                    if literal.token_flags.0 == 0
                        && literal.template_flags.0 == 0
                        && literal_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
                {
                    literal.text.clone()
                }
                _ => return Err(unsupported(expression, literal_record.kind)),
            };
            Ok((text, Some(expression)))
        }
        _ => Err(unsupported(name, record.kind)),
    }
}

fn validate_namespace_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    symbol: SemanticSymbolId,
    members: Option<super::SymbolTableId>,
    properties: &[JsxNamespaceProperty],
    indexes: &[JsxNamespaceIndex],
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceCheckError::Property(declaration))?;
    let super::TypeData::Interface(interface) = record.data() else {
        return Err(SourceCheckError::Property(declaration));
    };
    let expected_properties = properties
        .iter()
        .map(|property| property.symbol)
        .collect::<Vec<_>>();
    let existing_indexes = interface
        .reference
        .object
        .structured
        .index_infos
        .as_deref()
        .unwrap_or_default();
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(symbol)
        || !interface.base_types_resolved
        || !interface.declared_members_resolved
        || interface.declared_members != members
        || interface.reference.object.structured.members != members
        || interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap_or_default()
            != expected_properties.as_slice()
        || existing_indexes.len() != indexes.len()
    {
        return Err(SourceCheckError::Property(declaration));
    }
    for property in properties {
        if store
            .value_symbol_links(property.symbol)
            .and_then(|links| links.resolved_type)
            != Some(property.type_)
        {
            return Err(SourceCheckError::Property(declaration));
        }
    }
    for (identity, expected) in existing_indexes.iter().zip(indexes) {
        let info = store
            .index_info(*identity)
            .ok_or(SourceCheckError::Property(declaration))?;
        if info.key_type() != expected.key_type
            || info.value_type() != expected.value_type
            || info.declaration() != Some(expected.declaration)
        {
            return Err(SourceCheckError::Property(declaration));
        }
    }
    Ok(())
}

fn invalid_namespace_symbol(symbol: SemanticSymbolId) -> SourceCheckError {
    SourceCheckError::DeclaredType(super::DeclaredTypeError::Unavailable(
        super::DeclaredTypeUnavailable::SymbolNotOwned(symbol),
    ))
}

#[allow(clippy::too_many_lines)] // Preserve opening, closing, attribute, and child ordering.
fn execute_jsx_element(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    plan: &JsxElementPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let mut children_checked = false;
    if plan.expression != plan.opening {
        publish_jsx_links(
            store,
            plan.expression,
            JsxElementLinks {
                jsx_namespace: Some(namespace.unknown_symbol),
                ..JsxElementLinks::default()
            },
        )?;
    }

    match &plan.kind {
        JsxElementPlanKind::Fragment => {
            publish_jsx_links(
                store,
                plan.opening,
                JsxElementLinks {
                    jsx_namespace: Some(namespace.unknown_symbol),
                    ..JsxElementLinks::default()
                },
            )?;
        }
        JsxElementPlanKind::Element {
            tag,
            attributes_node,
            attributes,
            type_arguments,
            closing,
        } => {
            let (expected_attributes, signature) = if tag.intrinsic {
                let intrinsic = resolve_intrinsic_tag(
                    store,
                    bound,
                    namespace,
                    plan.opening,
                    tag,
                    options,
                    diagnostics,
                )?;
                let signature = intrinsic_signature(
                    store,
                    plan.opening,
                    intrinsic.attributes_type,
                    namespace.element_type,
                )?;
                publish_intrinsic_tag_links(
                    store,
                    arena,
                    tag,
                    namespace.any_type,
                    intrinsic.symbol,
                )?;
                publish_symbol_links(store, plan.opening, intrinsic.symbol)?;
                publish_jsx_links(
                    store,
                    plan.opening,
                    JsxElementLinks {
                        jsx_flags: intrinsic.flags,
                        resolved_jsx_element_attributes_type: Some(intrinsic.attributes_type),
                        jsx_namespace: Some(namespace.unknown_symbol),
                        jsx_implicit_import_container: None,
                    },
                )?;
                if !type_arguments.is_empty() {
                    emit_intrinsic_type_argument_diagnostic(
                        arena,
                        plan.opening,
                        type_arguments,
                        diagnostics,
                    )?;
                }
                if let Some(closing) = closing {
                    check_jsx_closing_tag(
                        store,
                        arena,
                        bound,
                        namespace,
                        closing,
                        options,
                        diagnostics,
                    )?;
                }
                (intrinsic.attributes_type, signature)
            } else {
                if !type_arguments.is_empty() {
                    return Err(unsupported(plan.opening, SyntaxKind::JsxOpeningElement));
                }
                let (attributes_type, signature) = resolve_component_tag(
                    store,
                    (arena, bound),
                    namespace,
                    plan.opening,
                    tag,
                    options,
                    diagnostics,
                )?;
                publish_jsx_links(
                    store,
                    plan.opening,
                    JsxElementLinks {
                        jsx_namespace: Some(namespace.unknown_symbol),
                        ..JsxElementLinks::default()
                    },
                )?;
                if let Some(closing) = closing {
                    check_jsx_closing_tag(
                        store,
                        arena,
                        bound,
                        namespace,
                        closing,
                        options,
                        diagnostics,
                    )?;
                }
                (attributes_type, signature)
            };

            publish_signature_links(store, plan.opening, signature)?;
            let children = if options.jsx_runtime == CanonicalJsxRuntime::Automatic {
                check_automatic_jsx_children(
                    store,
                    arena,
                    bound,
                    namespace,
                    plan,
                    attributes,
                    options,
                    diagnostics,
                )?
            } else {
                None
            };
            children_checked = children.is_some();
            let (checked, actual_attributes) = match attributes {
                JsxAttributesPlan::Properties(attributes) => {
                    let checked = check_jsx_attributes(
                        store,
                        (arena, bound),
                        namespace,
                        expected_attributes,
                        attributes,
                        options,
                        diagnostics,
                    )?;
                    let actual = publish_attribute_object(
                        store,
                        bound,
                        *attributes_node,
                        &checked,
                        children,
                    )?;
                    (checked, actual)
                }
                JsxAttributesPlan::ObjectSpread(spread) => {
                    let (checked, actual) = check_jsx_object_spread(
                        store,
                        (arena, bound),
                        namespace,
                        expected_attributes,
                        spread,
                        options,
                        diagnostics,
                    )?;
                    publish_type_links(store, *attributes_node, actual)?;
                    (checked, actual)
                }
            };
            check_attribute_assignability(
                store,
                (arena, bound),
                plan.opening,
                tag,
                (expected_attributes, actual_attributes),
                &checked,
                children,
                diagnostics,
            )?;
        }
    }

    if !children_checked {
        for child in &plan.children {
            match child {
                JsxChildPlan::Text { .. } => {}
                JsxChildPlan::Expression { wrapper, value } => {
                    let type_ = execute_scalar(
                        store,
                        arena,
                        bound,
                        namespace,
                        value,
                        options,
                        diagnostics,
                    )?;
                    publish_type_links(store, *wrapper, type_)?;
                }
                JsxChildPlan::Element(element) => {
                    execute_jsx_element(
                        store,
                        arena,
                        bound,
                        namespace,
                        element,
                        options,
                        diagnostics,
                    )?;
                }
            }
        }
    }

    publish_type_links(store, plan.expression, namespace.element_type)?;
    Ok(namespace.element_type)
}

#[allow(clippy::too_many_arguments)] // JSX child execution retains the enclosing checker state.
fn check_automatic_jsx_children(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    plan: &JsxElementPlan,
    attributes: &JsxAttributesPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Option<CheckedJsxChildren>, SourceCheckError> {
    let [child] = plan.children.as_slice() else {
        return if plan.children.is_empty() {
            Ok(None)
        } else {
            Err(unsupported(plan.expression, SyntaxKind::JsxElement))
        };
    };
    match attributes {
        JsxAttributesPlan::Properties(attributes)
            if attributes
                .iter()
                .any(|attribute| attribute.name == "children") =>
        {
            return Err(unsupported(plan.opening, SyntaxKind::JsxAttributes));
        }
        JsxAttributesPlan::ObjectSpread(spread) => {
            return Err(unsupported(spread.node, SyntaxKind::JsxSpreadAttribute));
        }
        JsxAttributesPlan::Properties(_) => {}
    }

    let (node, type_) = match child {
        JsxChildPlan::Text { node } => {
            let string_type = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .string_type;
            (*node, string_type)
        }
        JsxChildPlan::Expression { wrapper, value } => {
            let type_ =
                execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
            publish_type_links(store, *wrapper, type_)?;
            (*wrapper, type_)
        }
        JsxChildPlan::Element(element) => {
            let type_ = execute_jsx_element(
                store,
                arena,
                bound,
                namespace,
                element,
                options,
                diagnostics,
            )?;
            (element.expression, type_)
        }
    };
    Ok(Some(CheckedJsxChildren { node, type_ }))
}

fn check_jsx_closing_tag(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    closing: &JsxClosingPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    if closing.tag.intrinsic {
        let intrinsic = resolve_intrinsic_tag(
            store,
            bound,
            namespace,
            closing.node,
            &closing.tag,
            options,
            diagnostics,
        )?;
        publish_intrinsic_tag_links(
            store,
            arena,
            &closing.tag,
            namespace.any_type,
            intrinsic.symbol,
        )?;
        publish_symbol_links(store, closing.node, intrinsic.symbol)?;
        return publish_jsx_links(
            store,
            closing.node,
            JsxElementLinks {
                jsx_flags: intrinsic.flags,
                jsx_namespace: Some(namespace.unknown_symbol),
                ..JsxElementLinks::default()
            },
        );
    }

    let Some(symbol) = resolve_source_value_symbol(store, bound, &closing.tag.name) else {
        add_missing_component_diagnostic(
            store,
            bound,
            closing.tag.node,
            &closing.tag.name,
            diagnostics,
        )?;
        return publish_type_links(store, closing.tag.node, namespace.error_type);
    };
    let component_type = jsx_component_value_type(store, arena, bound, symbol, closing.tag.node)?;
    publish_symbol_links(store, closing.tag.node, symbol)?;
    publish_type_links(store, closing.tag.node, component_type)
}

fn publish_intrinsic_tag_links(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    tag: &JsxTagPlan,
    type_: TypeId,
    symbol: SemanticSymbolId,
) -> Result<(), SourceCheckError> {
    publish_type_links(store, tag.node, type_)?;
    publish_symbol_links(store, tag.node, symbol)?;
    if let Some(NodeData::JsxNamespacedName(name)) =
        arena.get(tag.node.node).map(|record| &record.data)
    {
        publish_type_links(store, child_ref(tag.node, name.namespace), type_)?;
        publish_type_links(store, child_ref(tag.node, name.name), type_)?;
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Named and indexed lookup must retain pinned precedence.
fn resolve_intrinsic_tag(
    store: &mut CanonicalTypeMapperStore,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    opening: NodeRef,
    tag: &JsxTagPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<JsxIntrinsicResolution, SourceCheckError> {
    let Some(intrinsic_elements) = namespace.intrinsic_elements else {
        if options.no_implicit_any {
            add_diagnostic(diagnostics, opening, 7026, ["IntrinsicElements"])?;
        }
        return Ok(JsxIntrinsicResolution {
            symbol: namespace.unknown_symbol,
            attributes_type: namespace.error_type,
            flags: JsxFlags::NONE,
        });
    };

    let (property, indexes, owner) = {
        let record = store
            .type_payload(intrinsic_elements)
            .ok_or(SourceCheckError::Property(opening))?;
        if !record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            return Err(SourceCheckError::Property(opening));
        }
        let structured = record
            .data()
            .structured()
            .ok_or(SourceCheckError::Property(opening))?;
        let property = structured
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(&tag.name));
        (
            property,
            structured.index_infos.clone().unwrap_or_default(),
            record.symbol(),
        )
    };

    if let Some(symbol) = property {
        let record = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Property(opening))?;
        let attributes_type = store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(SourceCheckError::Property(opening))?;
        if !record.flags().contains(SymbolFlags::PROPERTY)
            || store.type_payload(attributes_type).is_none()
        {
            return Err(SourceCheckError::Property(opening));
        }
        return Ok(JsxIntrinsicResolution {
            symbol,
            attributes_type,
            flags: JsxFlags::INTRINSIC_NAMED_ELEMENT,
        });
    }

    let string_type = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?
        .string_type;
    let mut patterned_index = None;
    let mut string_index = None;
    for index in indexes {
        let info = store
            .index_info(index)
            .ok_or(SourceCheckError::Property(opening))?;
        if info.key_type() == string_type {
            string_index.get_or_insert(index);
        } else if template_pattern_index_matches_name(store, info.key_type(), &tag.name)
            && patterned_index.replace(index).is_some()
        {
            return Err(unsupported(opening, SyntaxKind::IndexSignature));
        }
    }

    if let Some(index) = patterned_index.or(string_index) {
        let (key_type, value_type, declaration, existing) = {
            let info = store
                .index_info(index)
                .ok_or(SourceCheckError::Property(opening))?;
            (
                info.key_type(),
                info.value_type(),
                info.declaration(),
                info.index_symbol(),
            )
        };
        if key_type != string_type
            && !template_pattern_index_matches_name(store, key_type, &tag.name)
        {
            return Err(SourceCheckError::Property(opening));
        }
        let symbol = if let Some(symbol) = existing {
            validate_index_symbol(store, symbol, owner, declaration, value_type, opening)?;
            symbol
        } else {
            let declaration =
                declaration.ok_or_else(|| unsupported(opening, SyntaxKind::IndexSignature))?;
            if !bound.contains(declaration)
                || !store.try_reserve_checker_symbol_allocations(1, 0)
                || !store.try_reserve_value_symbol_links(1)
            {
                return Err(SourceCheckError::Property(opening));
            }
            let symbol = store
                .alloc_symbol(SymbolData {
                    flags: SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                    check_flags: CheckFlags::INDEX_SYMBOL,
                    name: EscapedName::internal(InternalSymbolName::Index),
                    declarations: Some(vec![declaration]),
                    value_declaration: Some(declaration),
                    members: None,
                    exports: None,
                    parent: owner,
                    export_symbol: None,
                })
                .ok_or(SourceCheckError::Property(opening))?;
            if !store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(value_type),
                    ..ValueSymbolLinks::default()
                },
            ) || !store.set_index_info_symbol(index, Some(symbol))
            {
                return Err(SourceCheckError::Property(opening));
            }
            symbol
        };
        return Ok(JsxIntrinsicResolution {
            symbol,
            attributes_type: value_type,
            flags: JsxFlags::INTRINSIC_INDEXED_ELEMENT,
        });
    }

    add_diagnostic(
        diagnostics,
        opening,
        2339,
        [tag.name.as_str(), "JSX.IntrinsicElements"],
    )?;
    Ok(JsxIntrinsicResolution {
        symbol: namespace.unknown_symbol,
        attributes_type: namespace.error_type,
        flags: JsxFlags::NONE,
    })
}

fn validate_index_symbol(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    owner: Option<SemanticSymbolId>,
    declaration: Option<NodeRef>,
    value_type: TypeId,
    opening: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Property(opening))?;
    if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        || record.check_flags() != CheckFlags::INDEX_SYMBOL
        || record.name() != InternalSymbolName::Index.as_ref()
        || record.parent() != owner
        || record.value_declaration() != declaration
        || store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            != Some(value_type)
    {
        return Err(SourceCheckError::Property(opening));
    }
    Ok(())
}

fn intrinsic_signature(
    store: &mut CanonicalTypeMapperStore,
    opening: NodeRef,
    attributes_type: TypeId,
    element_type: TypeId,
) -> Result<SignatureId, SourceCheckError> {
    if let Some(signature) = store
        .signature_links(opening)
        .and_then(|links| links.resolved_signature.signature())
    {
        let record = store
            .signature(signature)
            .ok_or(SourceCheckError::Call(opening))?;
        let [parameter] = record.parameters() else {
            return Err(SourceCheckError::Call(opening));
        };
        if !record.flags().is_empty()
            || record.declaration().is_some()
            || !record.type_parameters().is_empty()
            || record.this_parameter().is_some()
            || record.min_argument_count() != 1
            || record.resolved_return_type() != Some(element_type)
            || store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                != Some(attributes_type)
            || store.symbol(*parameter).is_none_or(|parameter| {
                parameter.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
                    || parameter.name().as_utf8() != Some("props")
            })
        {
            return Err(SourceCheckError::Call(opening));
        }
        return Ok(signature);
    }

    if !store.try_reserve_checker_symbol_allocations(1, 0)
        || !store.try_reserve_value_symbol_links(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(1)
    {
        return Err(SourceCheckError::Call(opening));
    }
    let parameter = store
        .alloc_symbol(SymbolData::new(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
            EscapedName::source("props"),
        ))
        .ok_or(SourceCheckError::Call(opening))?;
    if !store.set_value_symbol_links(
        parameter,
        ValueSymbolLinks {
            resolved_type: Some(attributes_type),
            ..ValueSymbolLinks::default()
        },
    ) {
        return Err(SourceCheckError::Call(opening));
    }
    store
        .alloc_signature(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            vec![parameter],
            Some(element_type),
            None,
            1,
        )
        .ok_or(SourceCheckError::Call(opening))
}

fn resolve_component_tag(
    store: &mut CanonicalTypeMapperStore,
    source: (&NodeArena, &BoundFile),
    namespace: &JsxNamespace,
    opening: NodeRef,
    tag: &JsxTagPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(TypeId, SignatureId), SourceCheckError> {
    let (arena, bound) = source;
    let Some(symbol) = resolve_source_value_symbol(store, bound, &tag.name) else {
        add_missing_component_diagnostic(store, bound, tag.node, &tag.name, diagnostics)?;
        let unknown_signature = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?
            .unknown_signature;
        publish_type_links(store, tag.node, namespace.error_type)?;
        return Ok((namespace.error_type, unknown_signature));
    };
    let component = jsx_component_value_type(store, arena, bound, symbol, tag.node)?;
    publish_symbol_links(store, tag.node, symbol)?;
    publish_type_links(store, tag.node, component)?;
    if component == namespace.any_type || component == namespace.error_type {
        let any_signature = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?
            .any_signature;
        return Ok((namespace.any_type, any_signature));
    }

    let callable = match validate_stored_callable_set(store, component) {
        StoredCallableSetValidation::Valid { projection, .. }
            if projection.construct_signatures.is_empty()
                && projection.call_signatures.len() == 1 =>
        {
            projection.call_signatures[0].clone()
        }
        StoredCallableSetValidation::NotCallable => {
            add_diagnostic(diagnostics, tag.node, 2604, [tag.name.as_str()])?;
            let unknown_signature = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .unknown_signature;
            return Ok((namespace.error_type, unknown_signature));
        }
        StoredCallableSetValidation::Pending { .. }
        | StoredCallableSetValidation::Malformed { .. }
        | StoredCallableSetValidation::Valid { .. } => {
            return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
        }
    };
    let signature = store
        .signature(callable.signature)
        .ok_or(SourceCheckError::Call(opening))?;
    if !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.has_rest_parameter()
        || callable.min_argument_count > 1
        || callable.parameters.len() > 1
    {
        return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
    }
    if callable.return_type.is_none() {
        let host =
            DeclaredTypeHost::new([(arena, bound)]).map_err(super::DeclaredTypeError::from)?;
        CanonicalTypeQuery::new(store, &host, options, diagnostics)?
            .get_return_type_of_signature(callable.signature)?;
    }
    let attributes_type = callable.parameters.first().copied().unwrap_or_else(|| {
        store
            .intrinsic_bootstrap()
            .expect("the checker bootstrap was validated")
            .empty_object_type
    });
    Ok((attributes_type, callable.signature))
}

fn jsx_component_value_type(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    symbol: SemanticSymbolId,
    location: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    if let Some(type_) = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
    {
        return Ok(type_);
    }

    let declaration = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::value_declaration)
        .ok_or(SourceCheckError::Call(location))?;
    let record = jsx_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(SourceCheckError::Call(location));
    };
    if let Some(initializer) = variable.initializer {
        let initializer = child_ref(declaration, initializer);
        let initializer_record = jsx_node(arena, bound, store, initializer)?;
        let unavailable = || unsupported(initializer, initializer_record.kind);
        if initializer_record.kind != SyntaxKind::ArrowFunction
            || initializer_record.parent != Some(declaration.node)
        {
            return Err(unavailable());
        }
        let owner = bound
            .symbol(initializer)
            .and_then(|owner| store.get_merged_symbol(owner))
            .ok_or_else(&unavailable)?;
        let callable = store
            .source_callable_type_for_declaration(initializer)
            .or_else(|| store.source_callable_type_for_owner(owner))
            .or_else(|| {
                store
                    .value_symbol_links(owner)
                    .and_then(|links| links.resolved_type)
            })
            .ok_or_else(&unavailable)?;
        let provenance = store
            .source_callable_provenance(callable)
            .ok_or_else(&unavailable)?;
        if provenance.family != super::store::SourceCallableFamily::ArrowFunction
            || provenance.declaration != initializer
            || provenance.owner_symbol != owner
            || store.source_callable_type_for_owner(owner) != Some(callable)
            || store
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type)
                != Some(callable)
        {
            return Err(unavailable());
        }
        return Ok(callable);
    }
    let annotation = variable
        .type_
        .map(|annotation| child_ref(declaration, annotation))
        .ok_or(SourceCheckError::Call(location))?;
    let annotation_record = jsx_node(arena, bound, store, annotation)?;
    if annotation_record.parent != Some(declaration.node) {
        return Err(SourceCheckError::Call(location));
    }
    if let Some(links) = store.type_node_links(annotation) {
        if let Some(type_) = links.resolved_type {
            return store
                .type_payload(type_)
                .map(|_| type_)
                .ok_or(SourceCheckError::Call(location));
        }
        if links != &TypeNodeLinks::default() {
            return Err(SourceCheckError::Call(location));
        }
    }

    if !matches!(&annotation_record.data, NodeData::KeywordTypeNode(_)) {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    match annotation_record.kind {
        SyntaxKind::AnyKeyword => Ok(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Ok(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Ok(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Ok(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Ok(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Ok(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Ok(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Ok(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Ok(bootstrap.undefined_type),
        SyntaxKind::NeverKeyword => Ok(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Ok(bootstrap.non_primitive_type),
        _ => Err(unsupported(annotation, annotation_record.kind)),
    }
}

fn add_missing_component_diagnostic(
    store: &CanonicalTypeMapperStore,
    bound: &BoundFile,
    node: NodeRef,
    name: &str,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let suggestion = bound
        .locals(bound.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| {
            get_spelling_suggestion(
                name,
                locals.iter().map(|(_, symbol)| symbol),
                |symbol| {
                    let symbol = store.symbol(*symbol)?;
                    symbol
                        .flags()
                        .intersects(SymbolFlags::VALUE)
                        .then(|| symbol.name().as_utf8())
                        .flatten()
                },
                |left, right| {
                    store
                        .symbol(*left)
                        .and_then(|symbol| symbol.name().as_utf8())
                        .cmp(
                            &store
                                .symbol(*right)
                                .and_then(|symbol| symbol.name().as_utf8()),
                        )
                },
            )
        });
    let Some(suggestion) = suggestion else {
        return add_diagnostic(diagnostics, node, 2304, [name]);
    };
    let suggestion_record = store
        .symbol(suggestion)
        .ok_or(SourceCheckError::Property(node))?;
    let suggestion_name = suggestion_record
        .name()
        .as_utf8()
        .ok_or(SourceCheckError::Property(node))?;
    let related_information = if let Some(declaration) = suggestion_record.value_declaration() {
        vec![CanonicalCheckerRelatedInformation {
            node: Some(declaration),
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2728).ok_or(SourceCheckError::MissingDiagnostic(2728))?,
                [suggestion_name],
            ),
        }]
    } else {
        Vec::new()
    };
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2552).ok_or(SourceCheckError::MissingDiagnostic(2552))?,
                [name, suggestion_name],
            ),
            related_information,
        },
    );
    Ok(())
}

fn resolve_source_value_symbol(
    store: &CanonicalTypeMapperStore,
    bound: &BoundFile,
    name: &str,
) -> Option<SemanticSymbolId> {
    bound
        .locals(bound.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(name))
        .or_else(|| {
            store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source(name))
        })
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .filter(|symbol| {
            store
                .symbol(*symbol)
                .is_some_and(|record| record.flags().intersects(SymbolFlags::VALUE))
        })
}

fn resolve_scoped_jsx_value_symbol(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    location: NodeRef,
    name: &str,
) -> Option<SemanticSymbolId> {
    let mut current = Some(location);
    while let Some(node) = current {
        let symbol = bound
            .locals(node)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .filter(|symbol| {
                store
                    .symbol(*symbol)
                    .is_some_and(|record| record.flags().intersects(SymbolFlags::VALUE))
            });
        if symbol.is_some() {
            return symbol;
        }
        current = arena
            .get(node.node)
            .and_then(|record| record.parent)
            .map(|parent| child_ref(node, parent));
    }
    resolve_source_value_symbol(store, bound, name)
}

fn check_jsx_attributes(
    store: &mut CanonicalTypeMapperStore,
    source: (&NodeArena, &BoundFile),
    namespace: &JsxNamespace,
    expected_attributes: TypeId,
    attributes: &[JsxAttributePlan],
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Vec<CheckedJsxAttribute>, SourceCheckError> {
    let (arena, bound) = source;
    let mut checked = Vec::with_capacity(attributes.len());
    let mut names = HashSet::with_capacity(attributes.len());
    for attribute in attributes {
        if !names.insert(attribute.name.as_str()) {
            add_diagnostic(
                diagnostics,
                attribute.name_node,
                17001,
                std::iter::empty::<&str>(),
            )?;
        }
        let type_ = match &attribute.value {
            JsxAttributeValue::ImplicitTrue => {
                store
                    .intrinsic_bootstrap()
                    .ok_or(SourceCheckError::LiteralCache(
                        SourceLiteralCacheError::BootstrapUninitialized,
                    ))?
                    .true_type
            }
            JsxAttributeValue::Expression { wrapper, value } => {
                let type_ =
                    execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
                if let Some(wrapper) = wrapper {
                    publish_type_links(store, *wrapper, type_)?;
                }
                widened_jsx_attribute_type(store, expected_attributes, attribute, type_)?
            }
        };
        publish_symbol_links(store, attribute.name_node, attribute.symbol)?;
        publish_type_links(store, attribute.name_node, type_)?;
        if let Some(NodeData::JsxNamespacedName(name)) = arena
            .get(attribute.name_node.node)
            .map(|record| &record.data)
        {
            publish_type_links(
                store,
                child_ref(attribute.name_node, name.namespace),
                namespace.error_type,
            )?;
            publish_type_links(
                store,
                child_ref(attribute.name_node, name.name),
                namespace.error_type,
            )?;
        }
        publish_attribute_value_links(store, attribute.symbol, type_, attribute.node)?;
        publish_type_links(store, attribute.node, type_)?;
        checked.push(CheckedJsxAttribute {
            plan: attribute.clone(),
            type_,
        });
    }
    Ok(checked)
}

fn check_jsx_object_spread(
    store: &mut CanonicalTypeMapperStore,
    source: (&NodeArena, &BoundFile),
    namespace: &JsxNamespace,
    expected_attributes: TypeId,
    spread: &JsxObjectSpreadPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(Vec<CheckedJsxAttribute>, TypeId), SourceCheckError> {
    let (arena, bound) = source;
    let mut checked = Vec::with_capacity(spread.properties.len());
    let mut property_types = Vec::with_capacity(spread.properties.len());

    for property in &spread.properties {
        let JsxAttributeValue::Expression {
            wrapper: None,
            value,
        } = &property.value
        else {
            return Err(SourceCheckError::Property(spread.node));
        };
        let value_type =
            execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
        let property_type =
            widened_jsx_attribute_type(store, expected_attributes, property, value_type)?;
        property_types.push(property_type);
        checked.push(CheckedJsxAttribute {
            plan: property.clone(),
            type_: property_type,
        });
    }

    let object =
        super::object_members::publish_object_literal(store, &spread.object, &property_types)
            .map_err(|_| SourceCheckError::Property(spread.object.node))?;
    for property in &checked {
        publish_symbol_links(store, property.plan.name_node, property.plan.symbol)?;
        publish_type_links(store, property.plan.name_node, property.type_)?;
    }

    Ok((checked, object))
}

fn widened_jsx_attribute_type(
    store: &CanonicalTypeMapperStore,
    expected_attributes: TypeId,
    attribute: &JsxAttributePlan,
    value: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let record = store
        .type_payload(value)
        .ok_or(SourceCheckError::Property(attribute.node))?;
    let expected = store
        .type_payload(expected_attributes)
        .and_then(|expected| expected.data().structured())
        .and_then(|expected| expected.members)
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&attribute.name))
        .and_then(|symbol| store.value_symbol_links(symbol))
        .and_then(|links| links.resolved_type);
    if expected.is_some_and(|expected| {
        store
            .type_payload(expected)
            .is_some_and(|target| target.flags().intersects(record.flags()))
    }) && let super::TypeData::Literal(literal) = record.data()
    {
        return Ok(literal.regular_type);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let flags = record.flags();
    Ok(if flags.intersects(TypeFlags::STRING_LITERAL) {
        bootstrap.string_type
    } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        bootstrap.number_type
    } else if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        bootstrap.bigint_type
    } else if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        bootstrap.boolean_type
    } else {
        value
    })
}

fn publish_attribute_value_links(
    store: &mut CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    type_: TypeId,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let expected = ValueSymbolLinks {
        resolved_type: Some(type_),
        ..ValueSymbolLinks::default()
    };
    if store
        .value_symbol_links(symbol)
        .is_some_and(|links| links != &ValueSymbolLinks::default() && links != &expected)
        || !store.set_value_symbol_links(symbol, expected)
    {
        return Err(SourceCheckError::Property(node));
    }
    Ok(())
}

fn execute_scalar(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    scalar: &JsxScalarPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let (node, type_) = match scalar {
        JsxScalarPlan::String { node, value } => {
            let regular = store.regular_string_literal_type(value.clone())?;
            (*node, store.fresh_type_of_literal_type(regular)?)
        }
        JsxScalarPlan::Number { node, value } => {
            let regular = store.regular_number_literal_type(*value)?;
            (*node, store.fresh_type_of_literal_type(regular)?)
        }
        JsxScalarPlan::Boolean { node, value } => {
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            (
                *node,
                if *value {
                    bootstrap.true_type
                } else {
                    bootstrap.false_type
                },
            )
        }
        JsxScalarPlan::Null(node) => {
            let null_type = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .null_type;
            (*node, null_type)
        }
        JsxScalarPlan::Identifier { node, name } => {
            let Some(symbol) = resolve_scoped_jsx_value_symbol(store, arena, bound, *node, name)
            else {
                add_diagnostic(diagnostics, *node, 2304, [name.as_str()])?;
                publish_type_links(store, *node, namespace.error_type)?;
                return Ok(namespace.error_type);
            };
            let type_ = store
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .or_else(|| {
                    let declaration = store.symbol(symbol)?.value_declaration()?;
                    if !declaration.is_for(arena.id(), bound.file_id())
                        || !bound.contains(declaration)
                    {
                        return None;
                    }
                    let NodeData::VariableDeclaration(variable) =
                        &arena.get(declaration.node)?.data
                    else {
                        return None;
                    };
                    let initializer = child_ref(declaration, variable.initializer?);
                    store
                        .type_node_links(initializer)
                        .and_then(|links| links.resolved_type)
                        .filter(|type_| store.type_payload(*type_).is_some())
                })
                .ok_or(SourceCheckError::Property(*node))?;
            publish_symbol_links(store, *node, symbol)?;
            (*node, type_)
        }
        JsxScalarPlan::Property {
            node,
            receiver,
            name_node,
            name,
        } => {
            let receiver_type = execute_scalar(
                store,
                arena,
                bound,
                namespace,
                receiver,
                options,
                diagnostics,
            )?;
            if receiver_type == namespace.any_type || receiver_type == namespace.error_type {
                (*node, receiver_type)
            } else if let Some(property) = store.resolved_own_property(receiver_type, name)? {
                if property.optional {
                    return Err(unsupported(*node, SyntaxKind::PropertyAccessExpression));
                }
                publish_symbol_links(store, *name_node, property.symbol)?;
                publish_type_links(store, *name_node, property.type_)?;
                publish_symbol_links(store, *node, property.symbol)?;
                (*node, property.type_)
            } else {
                let host = DeclaredTypeHost::new([(arena, bound)])
                    .map_err(super::DeclaredTypeError::from)?;
                let target = type_to_string_with_host_and_flags(
                    store,
                    &host,
                    receiver_type,
                    CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
                )?;
                add_diagnostic(
                    diagnostics,
                    *name_node,
                    2339,
                    [name.as_str(), target.as_str()],
                )?;
                (*node, namespace.error_type)
            }
        }
        JsxScalarPlan::AnyAssertion {
            node,
            type_node,
            value,
        } => {
            execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
            let any = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .any_type;
            publish_type_links(store, *type_node, any)?;
            (*node, any)
        }
        JsxScalarPlan::Parenthesized { node, value } => {
            let type_ =
                execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
            (*node, type_)
        }
        JsxScalarPlan::Conditional {
            node,
            condition,
            when_true,
            when_false,
        } => {
            execute_scalar(
                store,
                arena,
                bound,
                namespace,
                condition,
                options,
                diagnostics,
            )?;
            let true_type = execute_scalar(
                store,
                arena,
                bound,
                namespace,
                when_true,
                options,
                diagnostics,
            )?;
            let false_type = execute_scalar(
                store,
                arena,
                bound,
                namespace,
                when_false,
                options,
                diagnostics,
            )?;
            let type_ = if true_type == false_type {
                true_type
            } else {
                let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
                store.literal_union_type_prepared(&[true_type, false_type], None, &mut prepared)?
            };
            (*node, type_)
        }
        JsxScalarPlan::Element(element) => {
            return execute_jsx_element(
                store,
                arena,
                bound,
                namespace,
                element,
                options,
                diagnostics,
            );
        }
    };
    publish_type_links(store, node, type_)?;
    Ok(type_)
}

fn publish_attribute_object(
    store: &mut CanonicalTypeMapperStore,
    bound: &BoundFile,
    attributes_node: NodeRef,
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
) -> Result<TypeId, SourceCheckError> {
    let owner = bound
        .symbol(attributes_node)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(attributes_node),
        ))?;
    if let Some(type_) = store
        .type_node_links(attributes_node)
        .and_then(|links| links.resolved_type)
    {
        validate_attribute_object(store, type_, owner, attributes, children, attributes_node)?;
        return Ok(type_);
    }
    let property_count = attributes.len() + usize::from(children.is_some());
    if !store.try_reserve_checker_symbol_allocations(property_count, 1)
        || !store.try_reserve_value_symbol_links(property_count)
        || !store.try_reserve_types(1)
        || !store.try_reserve_type_node_links(1)
    {
        return Err(SourceCheckError::Property(attributes_node));
    }
    let members = store.alloc_symbol_table();
    let mut properties = Vec::with_capacity(property_count);
    for attribute in attributes {
        let data = {
            let source = store
                .symbol(attribute.plan.symbol)
                .ok_or(SourceCheckError::Property(attribute.plan.node))?;
            SymbolData {
                flags: SymbolFlags::PROPERTY | source.flags() | SymbolFlags::TRANSIENT,
                check_flags: source.check_flags(),
                name: EscapedName::source(&attribute.plan.name),
                declarations: source.declarations().map(<[NodeRef]>::to_vec),
                value_declaration: source.value_declaration(),
                members: None,
                exports: None,
                parent: source.parent(),
                export_symbol: None,
            }
        };
        let symbol = store
            .alloc_symbol(data)
            .ok_or(SourceCheckError::Property(attribute.plan.node))?;
        if !store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(attribute.type_),
                target: Some(attribute.plan.symbol),
                ..ValueSymbolLinks::default()
            },
        ) || store
            .insert_symbol(members, EscapedName::source(&attribute.plan.name), symbol)
            .is_none()
        {
            return Err(SourceCheckError::Property(attribute.plan.node));
        }
        properties.push(symbol);
    }
    if let Some(children) = children {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                EscapedName::source("children"),
            ))
            .ok_or(SourceCheckError::Property(children.node))?;
        if !store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(children.type_),
                ..ValueSymbolLinks::default()
            },
        ) || store
            .insert_symbol(members, EscapedName::source("children"), symbol)
            .is_none()
        {
            return Err(SourceCheckError::Property(children.node));
        }
        properties.push(symbol);
    }
    let flags = ObjectFlags::ANONYMOUS
        | ObjectFlags::OBJECT_LITERAL
        | ObjectFlags::FRESH_LITERAL
        | ObjectFlags::JSX_ATTRIBUTES
        | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
    let type_ = store
        .alloc_plain_object_type(flags, Some(owner))
        .ok_or(SourceCheckError::Property(attributes_node))?;
    if !store.set_structured_type_members(
        type_,
        Some(members),
        (!properties.is_empty()).then_some(properties),
        None,
        None,
        None,
    ) {
        return Err(SourceCheckError::Property(attributes_node));
    }
    publish_type_links(store, attributes_node, type_)?;
    Ok(type_)
}

fn validate_attribute_object(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    owner: SemanticSymbolId,
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceCheckError::Property(node))?;
    if record.symbol() != Some(owner)
        || !record.object_flags().contains(
            ObjectFlags::ANONYMOUS
                | ObjectFlags::OBJECT_LITERAL
                | ObjectFlags::FRESH_LITERAL
                | ObjectFlags::JSX_ATTRIBUTES
                | ObjectFlags::MEMBERS_RESOLVED,
        )
    {
        return Err(SourceCheckError::Property(node));
    }
    let structured = record
        .data()
        .structured()
        .ok_or(SourceCheckError::Property(node))?;
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourceCheckError::Property(node))?;
    if structured.properties.as_deref().unwrap_or_default().len()
        != attributes.len() + usize::from(children.is_some())
    {
        return Err(SourceCheckError::Property(node));
    }
    for attribute in attributes {
        let property = members
            .get_source(&attribute.plan.name)
            .ok_or(SourceCheckError::Property(node))?;
        let links = store
            .value_symbol_links(property)
            .ok_or(SourceCheckError::Property(node))?;
        if links.resolved_type != Some(attribute.type_)
            || links.target != Some(attribute.plan.symbol)
        {
            return Err(SourceCheckError::Property(node));
        }
    }
    if let Some(children) = children {
        let symbol = members
            .get_source("children")
            .ok_or(SourceCheckError::Property(node))?;
        let record = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Property(node))?;
        if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some("children")
            || record.declarations().is_some()
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol().is_some()
            || store.value_symbol_links(symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(children.type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(SourceCheckError::Property(node));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // Attribute diagnostics retain the implicit child property.
fn check_attribute_assignability(
    store: &mut CanonicalTypeMapperStore,
    source: (&NodeArena, &BoundFile),
    opening: NodeRef,
    tag: &JsxTagPlan,
    (expected, actual): (TypeId, TypeId),
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let expected_record = store
        .type_payload(expected)
        .ok_or(SourceCheckError::Property(opening))?;
    if expected_record.flags().intersects(TypeFlags::ANY) {
        return Ok(());
    }
    let structured = expected_record
        .data()
        .structured()
        .ok_or_else(|| unsupported(opening, SyntaxKind::JsxAttributes))?;
    let expected_members = structured.members;
    let required = structured.properties.clone().unwrap_or_default();
    let index_infos = structured.index_infos.clone().unwrap_or_default();
    let mut present = HashSet::with_capacity(attributes.len());
    let mut has_excess_attribute = false;
    for attribute in attributes {
        present.insert(attribute.plan.name.as_str());
        let expected_property = expected_members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(&attribute.plan.name));
        let expected_type = if let Some(property) = expected_property {
            store
                .value_symbol_links(property)
                .and_then(|links| links.resolved_type)
                .ok_or(SourceCheckError::Property(attribute.plan.node))?
        } else if let Some(type_) =
            matching_attribute_index_value_type(store, &index_infos, &attribute.plan.name)?
        {
            type_
        } else if attribute.plan.name.contains('-') {
            continue;
        } else {
            has_excess_attribute = true;
            let host = DeclaredTypeHost::new([source]).map_err(super::DeclaredTypeError::from)?;
            let target = type_to_string_with_host_and_flags(
                store,
                &host,
                expected,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )?;
            let detail = Diagnostic::with_arguments(
                message_by_code(2339).ok_or(SourceCheckError::MissingDiagnostic(2339))?,
                [attribute.plan.name.as_str(), target.as_str()],
            )
            .render()
            .map_err(|_| SourceCheckError::MissingDiagnostic(2339))?;
            let diagnostic = Diagnostic::with_arguments(
                message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                [
                    format_attribute_object(store, &host, attributes, children)?,
                    target,
                ],
            )
            .with_details([format!("  {detail}")]);
            merge_retry_diagnostic(
                diagnostics,
                CanonicalCheckerDiagnostic {
                    node: Some(attribute.plan.name_node),
                    range_override: None,
                    diagnostic,
                    related_information: Vec::new(),
                },
            );
            continue;
        };
        if !store.is_type_assignable_to(attribute.type_, expected_type)? {
            let display =
                get_type_names_for_assignability_error(store, attribute.type_, expected_type)?;
            add_diagnostic(
                diagnostics,
                attribute.plan.name_node,
                2322,
                [display.source, display.target],
            )?;
        }
    }

    if let Some(children) = children {
        present.insert("children");
        if let Some(expected_type) = expected_members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("children"))
            .and_then(|symbol| store.value_symbol_links(symbol))
            .and_then(|links| links.resolved_type)
            && !store.is_type_assignable_to(children.type_, expected_type)?
        {
            let display =
                get_type_names_for_assignability_error(store, children.type_, expected_type)?;
            add_diagnostic(
                diagnostics,
                children.node,
                2322,
                [display.source, display.target],
            )?;
        }
    }

    if !has_excess_attribute {
        for property in required {
            let record = store
                .symbol(property)
                .ok_or(SourceCheckError::Property(opening))?;
            if record.flags().contains(SymbolFlags::OPTIONAL) {
                continue;
            }
            let name = record
                .name()
                .as_utf8()
                .ok_or(SourceCheckError::Property(opening))?;
            if !present.contains(name) {
                let host =
                    DeclaredTypeHost::new([source]).map_err(super::DeclaredTypeError::from)?;
                let source = format_attribute_object(store, &host, attributes, children)?;
                let target = type_to_string_with_host_and_flags(
                    store,
                    &host,
                    expected,
                    CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
                )?;
                if children.is_some() {
                    let declaration = record
                        .value_declaration()
                        .or_else(|| {
                            record
                                .declarations()
                                .and_then(|nodes| nodes.first().copied())
                        })
                        .ok_or(SourceCheckError::Property(opening))?;
                    let declaration_record = host
                        .node(declaration)
                        .ok_or(SourceCheckError::Property(declaration))?;
                    let name_node = match &declaration_record.data {
                        NodeData::PropertyDeclaration(property) => {
                            child_ref(declaration, property.name)
                        }
                        NodeData::PropertySignatureDeclaration(property) => {
                            child_ref(declaration, property.name)
                        }
                        _ => return Err(SourceCheckError::Property(declaration)),
                    };
                    merge_retry_diagnostic(
                        diagnostics,
                        CanonicalCheckerDiagnostic {
                            node: Some(tag.node),
                            range_override: None,
                            diagnostic: Diagnostic::with_arguments(
                                message_by_code(2741)
                                    .ok_or(SourceCheckError::MissingDiagnostic(2741))?,
                                [name, source.as_str(), target.as_str()],
                            ),
                            related_information: vec![CanonicalCheckerRelatedInformation {
                                node: Some(name_node),
                                diagnostic: Diagnostic::with_arguments(
                                    message_by_code(2728)
                                        .ok_or(SourceCheckError::MissingDiagnostic(2728))?,
                                    [name],
                                ),
                            }],
                        },
                    );
                } else {
                    add_diagnostic(diagnostics, tag.node, 2741, [name, &source, &target])?;
                }
            }
        }
    }

    if store.type_payload(actual).is_none() {
        return Err(SourceCheckError::Property(opening));
    }
    Ok(())
}

fn matching_attribute_index_value_type(
    store: &CanonicalTypeMapperStore,
    indexes: &[super::IndexInfoId],
    name: &str,
) -> Result<Option<TypeId>, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let mut string_index = None;
    for index in indexes {
        let Some(info) = store.index_info(*index) else {
            return Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::Capacity,
            ));
        };
        if info.key_type() == bootstrap.string_type {
            string_index.get_or_insert(info.value_type());
        } else if template_pattern_index_matches_name(store, info.key_type(), name) {
            return Ok(Some(info.value_type()));
        }
    }
    Ok(string_index)
}

fn format_attribute_object(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
) -> Result<String, SourceCheckError> {
    if attributes.is_empty() && children.is_none() {
        return Ok("{}".to_owned());
    }
    let mut names = attributes
        .iter()
        .map(|attribute| -> Result<String, SourceCheckError> {
            let name = if attribute.plan.name.contains(':') {
                format!("\"{}\"", attribute.plan.name)
            } else {
                attribute.plan.name.clone()
            };
            Ok(format!(
                "{name}: {};",
                type_to_string_with_host_and_flags(
                    store,
                    host,
                    attribute.type_,
                    CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
                )?
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(children) = children {
        names.push(format!(
            "children: {};",
            type_to_string_with_host_and_flags(
                store,
                host,
                children.type_,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )?
        ));
    }
    Ok(format!("{{ {} }}", names.join(" ")))
}

fn emit_intrinsic_type_argument_diagnostic(
    arena: &NodeArena,
    opening: NodeRef,
    arguments: &[NodeRef],
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let first = arguments
        .first()
        .and_then(|node| arena.get(node.node))
        .ok_or(SourceCheckError::Call(opening))?;
    let last = arguments
        .last()
        .and_then(|node| arena.get(node.node))
        .ok_or(SourceCheckError::Call(opening))?;
    let range = CanonicalCheckerDiagnosticRange::new(
        opening,
        TextRange::new(first.range.start, last.range.end),
    );
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(opening),
            range_override: Some(range),
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2558).ok_or(SourceCheckError::MissingDiagnostic(2558))?,
                ["0".to_owned(), arguments.len().to_string()],
            ),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn publish_type_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> Result<(), SourceCheckError> {
    let expected = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected)
        || !store.set_type_node_links(node, expected)
    {
        return Err(SourceCheckError::Property(node));
    }
    Ok(())
}

fn publish_symbol_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), SourceCheckError> {
    let expected = SymbolNodeLinks {
        resolved_symbol: Some(symbol),
    };
    if store
        .symbol_node_links(node)
        .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected)
        || !store.set_symbol_node_links(node, expected)
    {
        return Err(SourceCheckError::Property(node));
    }
    Ok(())
}

fn publish_jsx_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    links: JsxElementLinks,
) -> Result<(), SourceCheckError> {
    if store
        .jsx_element_links(node)
        .is_some_and(|current| current != &JsxElementLinks::default() && current != &links)
        || !store.set_jsx_element_links(node, links)
    {
        return Err(SourceCheckError::Property(node));
    }
    Ok(())
}

fn publish_signature_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    signature: SignatureId,
) -> Result<(), SourceCheckError> {
    let expected = SignatureLinks {
        resolved_signature: ResolvedSignatureState::Resolved(signature),
        ..SignatureLinks::default()
    };
    if store
        .signature_links(node)
        .is_some_and(|current| current != &SignatureLinks::default() && current != &expected)
        || !store.set_signature_links(node, expected)
    {
        return Err(SourceCheckError::Call(node));
    }
    Ok(())
}

fn add_diagnostic(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    code: u32,
    arguments: impl IntoIterator<Item = impl Into<String>>,
) -> Result<(), SourceCheckError> {
    let message = message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(message, arguments),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn jsx_node<'arena>(
    arena: &'arena NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<&'arena ts_ast::Node, SourceCheckError> {
    if !node.is_for(arena.id(), bound.file_id())
        || !bound.contains(node)
        || !store.contains_node_ref(node)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::NodeNotBound(node),
        ));
    }
    let record = arena.get(node.node).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingNode(node),
    ))?;
    if !record.data.matches_syntax_kind(record.kind) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node,
                kind: record.kind,
            },
        ));
    }
    Ok(record)
}

fn child_ref(parent: NodeRef, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parent.arena, parent.file, node)
}

fn is_intrinsic_name(name: &str) -> bool {
    name.as_bytes().first().is_some_and(u8::is_ascii_lowercase) || name.contains('-')
}

fn unsupported(node: NodeRef, kind: SyntaxKind) -> SourceCheckError {
    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
        node,
        kind,
        role: SourceSyntaxRole::VariableInitializer,
    })
}

#[cfg(test)]
mod runtime_tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_jsx_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions,
        formatter::type_to_string,
        production::{CanonicalJsxRuntime, GlobalMergeCompletion},
    };

    struct RuntimeFixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl RuntimeFixture {
        fn new(source: &str, file: FileId) -> Self {
            let parsed = parse_jsx_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/runtime.tsx\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
            let bound = files.remove(&file).unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn expression(&self, name: &str) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) =
                        &self.parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        variable.initializer?,
                    ))
                })
                .unwrap_or_else(|| panic!("missing JSX variable {name}"))
        }

        fn check(
            &mut self,
            expression: NodeRef,
            runtime: CanonicalJsxRuntime,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) {
            let evidence = match runtime {
                CanonicalJsxRuntime::Preserve => CanonicalJsxRuntimeEvidence::Preserve,
                CanonicalJsxRuntime::Classic => CanonicalJsxRuntimeEvidence::Classic {
                    factory_namespace: "React",
                    fragment_factory_namespace: "React",
                    fragment_factory_required: false,
                    fragment_factory_pragma_required: false,
                },
                CanonicalJsxRuntime::Automatic => CanonicalJsxRuntimeEvidence::Automatic {
                    module_specifier: "react/jsx-runtime",
                    resolved_module: None,
                },
            };
            self.check_with_evidence(expression, runtime, evidence, diagnostics);
        }

        fn check_with_evidence(
            &mut self,
            expression: NodeRef,
            runtime: CanonicalJsxRuntime,
            evidence: CanonicalJsxRuntimeEvidence<'_>,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) {
            let runtime_diagnostics = source_jsx_runtime_diagnostics(
                &self.store,
                &self.parsed.arena,
                &self.bound,
                evidence,
            )
            .unwrap();
            for diagnostic in runtime_diagnostics.into_vec() {
                merge_retry_diagnostic(diagnostics, diagnostic);
            }
            let host = DeclaredTypeHost::new([(&self.parsed.arena, &self.bound)]).unwrap();
            self.store
                .check_jsx_element(
                    &host,
                    expression,
                    CanonicalCheckerOptions {
                        no_implicit_any: true,
                        jsx_runtime: runtime,
                        ..CanonicalCheckerOptions::default()
                    },
                    diagnostics,
                )
                .unwrap();
        }
    }

    #[test]
    fn classic_runtime_reports_missing_react_on_each_opening_tag_name() {
        let mut fixture = RuntimeFixture::new(
            "const first = <div>&amp;</div>;\nconst second = <div>text</div>;\n",
            FileId::new(8_100),
        );
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(first, CanonicalJsxRuntime::Classic, &mut diagnostics);
        fixture.check(second, CanonicalJsxRuntime::Classic, &mut diagnostics);

        let factory = diagnostics
            .as_slice()
            .iter()
            .filter(|diagnostic| diagnostic.diagnostic.code() == 2874)
            .collect::<Vec<_>>();
        assert_eq!(factory.len(), 2);
        for diagnostic in factory {
            let node = diagnostic.node.unwrap();
            let record = fixture.parsed.arena.get(node.node).unwrap();
            assert_eq!(record.kind, SyntaxKind::Identifier);
            let NodeData::Identifier(identifier) = &record.data else {
                unreachable!("the runtime diagnostic is on the JSX tag")
            };
            assert_eq!(identifier.text, "div");
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "This JSX tag requires 'React' to be in scope, but it could not be found.",
            );
        }
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .filter(|diagnostic| diagnostic.diagnostic.code() == 7026)
                .count(),
            4,
        );
    }

    #[test]
    fn classic_runtime_accepts_an_in_scope_react_factory() {
        let mut fixture = RuntimeFixture::new(
            "declare var React: any;\nconst view = <div></div>;\n",
            FileId::new(8_101),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [7026, 7026],
        );
    }

    #[test]
    fn automatic_runtime_reports_once_before_component_spelling_recovery() {
        let mut fixture = RuntimeFixture::new(
            "const app = <App />;\nconst next = <App />;\n",
            FileId::new(8_102),
        );
        let first = fixture.expression("app");
        let second = fixture.expression("next");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(first, CanonicalJsxRuntime::Automatic, &mut diagnostics);
        fixture.check(second, CanonicalJsxRuntime::Automatic, &mut diagnostics);

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2875, 2552, 2552],
        );
        let runtime = &diagnostics.as_slice()[0];
        assert_eq!(runtime.node, Some(first));
        assert_eq!(
            runtime.diagnostic.render().unwrap(),
            "This JSX tag requires the module path 'react/jsx-runtime' to exist, but none could be found. Make sure you have types for the appropriate package installed.",
        );
        let suggestion = &diagnostics.as_slice()[1];
        assert_eq!(suggestion.related_information.len(), 1);
        assert_eq!(suggestion.related_information[0].diagnostic.code(), 2728);
        assert!(
            fixture
                .store
                .jsx_element_links(fixture.bound.source_file())
                .is_none()
        );

        fixture.check(first, CanonicalJsxRuntime::Automatic, &mut diagnostics);
        assert_eq!(diagnostics.len(), 3);
    }

    #[test]
    fn classic_runtime_uses_the_exact_custom_factory_namespace() {
        let mut fixture = RuntimeFixture::new("const view = <foo />;\n", FileId::new(8_103));
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check_with_evidence(
            expression,
            CanonicalJsxRuntime::Classic,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "myReactLib",
                fragment_factory_namespace: "myReactLib",
                fragment_factory_required: false,
                fragment_factory_pragma_required: false,
            },
            &mut diagnostics,
        );

        let factory = diagnostics
            .as_slice()
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == 2874)
            .unwrap();
        assert_eq!(
            factory.diagnostic.render().unwrap(),
            "This JSX tag requires 'myReactLib' to be in scope, but it could not be found.",
        );
    }

    #[test]
    fn classic_runtime_accepts_an_exact_custom_factory_in_scope() {
        let mut fixture = RuntimeFixture::new(
            "declare var createElement: any;\nconst view = <foo />;\n",
            FileId::new(8_104),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check_with_evidence(
            expression,
            CanonicalJsxRuntime::Classic,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "createElement",
                fragment_factory_namespace: "createElement",
                fragment_factory_required: false,
                fragment_factory_pragma_required: false,
            },
            &mut diagnostics,
        );

        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 7026)
        );
    }

    #[test]
    fn classic_runtime_reports_missing_element_and_fragment_factories() {
        let fixture = RuntimeFixture::new("const view = <></>;\n", FileId::new(8_108));
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "React",
                fragment_factory_namespace: "React",
                fragment_factory_required: false,
                fragment_factory_pragma_required: false,
            },
        )
        .unwrap();

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2874, 2879],
        );
        for diagnostic in diagnostics.as_slice() {
            assert_eq!(
                fixture
                    .parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .kind,
                SyntaxKind::JsxOpeningFragment,
            );
        }
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "This JSX tag requires 'React' to be in scope, but it could not be found.",
        );
        assert_eq!(
            diagnostics.as_slice()[1].diagnostic.render().unwrap(),
            "Using JSX fragments requires fragment factory 'React' to be in scope, but it could not be found.",
        );
    }

    #[test]
    fn classic_runtime_reports_a_required_factory_on_each_entire_fragment() {
        let fixture = RuntimeFixture::new(
            "declare var h: any;\nconst first = <></>;\nconst second = <><span /><><span /></></>;\n",
            FileId::new(8_109),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "h",
                fragment_factory_namespace: "h",
                fragment_factory_required: true,
                fragment_factory_pragma_required: false,
            },
        )
        .unwrap();

        assert_eq!(diagnostics.len(), 3);
        for diagnostic in diagnostics.as_slice() {
            assert_eq!(diagnostic.diagnostic.code(), 17_016);
            assert_eq!(
                fixture
                    .parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .kind,
                SyntaxKind::JsxFragment,
            );
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "The 'jsxFragmentFactory' compiler option must be provided to use JSX fragments with the 'jsxFactory' compiler option.",
            );
        }
    }

    #[test]
    fn classic_runtime_requires_a_fragment_pragma_on_the_entire_fragment() {
        let fixture = RuntimeFixture::new(
            "declare var dom: any;\nconst view = <><h></h></>;\n",
            FileId::new(8_112),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "dom",
                fragment_factory_namespace: "React",
                fragment_factory_required: false,
                fragment_factory_pragma_required: true,
            },
        )
        .unwrap();

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2874, 2879, 17_017],
        );
        for diagnostic in &diagnostics.as_slice()[..2] {
            assert_eq!(
                fixture
                    .parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .kind,
                SyntaxKind::JsxOpeningFragment,
            );
        }
        let required = &diagnostics.as_slice()[2];
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(required.node.unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::JsxFragment,
        );
        assert_eq!(
            required.diagnostic.render().unwrap(),
            "An @jsxFrag pragma is required when using an @jsx pragma with JSX fragments.",
        );
    }

    #[test]
    fn classic_runtime_keeps_configured_factory_errors_before_pragma_errors() {
        let fixture = RuntimeFixture::new(
            "declare var createElement: any;\nconst view = <></>;\n",
            FileId::new(8_113),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "createElement",
                fragment_factory_namespace: "createElement",
                fragment_factory_required: true,
                fragment_factory_pragma_required: true,
            },
        )
        .unwrap();

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 17_016);
    }

    #[test]
    fn classic_runtime_resolves_the_exact_custom_fragment_factory_namespace() {
        let fixture = RuntimeFixture::new(
            "declare var createElement: any;\nconst view = <></>;\n",
            FileId::new(8_110),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "createElement",
                fragment_factory_namespace: "CustomFragments",
                fragment_factory_required: false,
                fragment_factory_pragma_required: false,
            },
        )
        .unwrap();

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2874, 2879],
        );
        assert!(diagnostics.as_slice().iter().all(|diagnostic| {
            diagnostic
                .diagnostic
                .render()
                .unwrap()
                .contains("'CustomFragments'")
        }));
    }

    #[test]
    fn classic_runtime_accepts_a_null_fragment_factory() {
        let fixture = RuntimeFixture::new(
            "declare var createElement: any;\nconst view = <></>;\n",
            FileId::new(8_111),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace: "createElement",
                fragment_factory_namespace: "null",
                fragment_factory_required: false,
                fragment_factory_pragma_required: false,
            },
        )
        .unwrap();

        assert!(diagnostics.is_empty());
    }

    #[test]
    fn empty_fragment_leaves_intrinsic_interface_cold_until_a_nested_tag_needs_it() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface Element {}\n",
                "  interface IntrinsicElements { unsupported(): void; }\n",
                "}\n",
                "const empty = <></>;\n",
                "const nested = <><div /></>;\n",
            ),
            FileId::new(8_134),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let empty = fixture.expression("empty");
        let nested = fixture.expression("nested");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(empty, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert!(diagnostics.is_empty());
        assert!(fixture.store.declared_type_links(intrinsics).is_none());
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
        );
        fixture.check(empty, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
            ),
            cold,
        );

        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let error = fixture
            .store
            .check_jsx_element(
                &host,
                nested,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();
        assert!(matches!(
            error,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                kind: SyntaxKind::MethodSignature,
                ..
            })
        ));
    }

    #[test]
    fn fragment_resolves_inherited_element_identity_without_expanding_intrinsics() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace React { interface ReactElement<Props, Kind> {} }\n",
                "declare namespace JSX {\n",
                "  interface Element extends React.ReactElement<any, any> {}\n",
                "  interface IntrinsicElements { unsupported(): void; }\n",
                "}\n",
                "const view = <>\n  </>;\n",
            ),
            FileId::new(8_135),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        for name in ["React", "JSX"] {
            let symbol = fixture
                .store
                .symbol_table(locals)
                .and_then(|locals| locals.get_source(name))
                .unwrap();
            assert_eq!(
                fixture
                    .store
                    .insert_symbol(globals, EscapedName::source(name), symbol),
                Some(None),
            );
        }
        let jsx = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("JSX"))
            .unwrap();
        let exports = fixture.store.symbol(jsx).unwrap().exports().unwrap();
        let element = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("Element"))
            .unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let expression = fixture.expression("view");
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let element_type = fixture
            .store
            .check_jsx_element(
                &host,
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();

        assert!(diagnostics.is_empty());
        assert_eq!(
            fixture
                .store
                .declared_type_links(element)
                .and_then(|links| links.declared_type),
            Some(element_type),
        );
        assert_eq!(
            fixture.store.type_payload(element_type).unwrap().symbol(),
            Some(element),
        );
        assert!(fixture.store.declared_type_links(intrinsics).is_none());

        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
        );
        assert_eq!(
            fixture
                .store
                .check_jsx_element(
                    &host,
                    expression,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap(),
            element_type,
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
            ),
            cold,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Validate computed keys and all intrinsic symbol locations.
    fn computed_intrinsic_names_keep_literal_types_and_opening_closing_symbols() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare var React: any;\n",
                "declare namespace JSX {\n",
                "  interface IntrinsicElements {\n",
                "    [\"package\"]: any;\n",
                "    [7]: any;\n",
                "    [`widget`]: any;\n",
                "  }\n",
                "}\n",
                "const first = <package />;\n",
                "const second = <package></package>;\n",
                "const third = <widget />;\n",
            ),
            FileId::new(8_125),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let third = fixture.expression("third");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [first, second, third] {
            fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);
        }

        assert!(diagnostics.is_empty());
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let members = fixture.store.symbol(intrinsics).unwrap().members().unwrap();
        let package = fixture
            .store
            .symbol_table(members)
            .and_then(|members| members.get_source("package"))
            .unwrap();
        let widget = fixture
            .store
            .symbol_table(members)
            .and_then(|members| members.get_source("widget"))
            .unwrap();

        for (expression, expected) in [(first, package), (third, widget)] {
            let NodeData::JsxSelfClosingElement(element) =
                &fixture.parsed.arena.get(expression.node).unwrap().data
            else {
                unreachable!("the fixture contains a self-closing intrinsic")
            };
            let name = child_ref(expression, element.tag_name);
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(expression)
                    .and_then(|links| links.resolved_symbol),
                Some(expected),
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol),
                Some(expected),
            );
        }

        let NodeData::JsxElement(paired) = &fixture.parsed.arena.get(second.node).unwrap().data
        else {
            unreachable!("the fixture contains a paired intrinsic")
        };
        let opening = child_ref(second, paired.opening_element);
        let closing = child_ref(second, paired.closing_element);
        let NodeData::JsxOpeningElement(opening_data) =
            &fixture.parsed.arena.get(opening.node).unwrap().data
        else {
            unreachable!("the paired intrinsic has an opening tag")
        };
        let NodeData::JsxClosingElement(closing_data) =
            &fixture.parsed.arena.get(closing.node).unwrap().data
        else {
            unreachable!("the paired intrinsic has a closing tag")
        };
        for node in [
            opening,
            child_ref(opening, opening_data.tag_name),
            closing,
            child_ref(closing, closing_data.tag_name),
        ] {
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                Some(package),
            );
        }

        let mut literals = Vec::new();
        for (_, record) in fixture.parsed.arena.iter() {
            let NodeData::ComputedPropertyName(computed) = &record.data else {
                continue;
            };
            let literal =
                NodeRef::new(fixture.parsed.arena.id(), fixture.file, computed.expression);
            let type_ = fixture
                .store
                .type_node_links(literal)
                .and_then(|links| links.resolved_type)
                .unwrap();
            literals.push(type_to_string(&fixture.store, type_).unwrap());
        }
        assert_eq!(literals, ["\"package\"", "7", "\"widget\""]);

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        for expression in [first, second, third] {
            fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                diagnostics.as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn dynamic_computed_intrinsic_names_remain_a_typed_boundary() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare const key: string;\n",
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { [key]: any; }\n",
                "}\n",
                "const view = <div />;\n",
            ),
            FileId::new(8_126),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let expression = fixture.expression("view");
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let error = fixture
            .store
            .check_jsx_element(
                &host,
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();

        assert!(matches!(
            error,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                kind: SyntaxKind::Identifier,
                ..
            })
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn namespaced_intrinsic_tags_publish_identifier_types_and_replay_warm() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { \"NS:Widget\": any; }\n",
                "}\n",
                "const first = <NS:Widget />;\n",
                "const second = <NS:Widget></NS:Widget>;\n",
            ),
            FileId::new(8_127),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [first, second] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }

        assert!(diagnostics.is_empty());
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let members = fixture.store.symbol(intrinsics).unwrap().members().unwrap();
        let expected = fixture
            .store
            .symbol_table(members)
            .and_then(|members| members.get_source("NS:Widget"))
            .unwrap();
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        let mut namespaced_count = 0;
        for (node, record) in fixture.parsed.arena.iter() {
            let NodeData::JsxNamespacedName(name) = &record.data else {
                continue;
            };
            namespaced_count += 1;
            let tag = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(tag)
                    .and_then(|links| links.resolved_symbol),
                Some(expected),
            );
            for identifier in [name.namespace, name.name] {
                let identifier = child_ref(tag, identifier);
                assert_eq!(
                    fixture
                        .store
                        .type_node_links(identifier)
                        .and_then(|links| links.resolved_type),
                    Some(any),
                );
                assert!(fixture.store.symbol_node_links(identifier).is_none());
            }
        }
        assert_eq!(namespaced_count, 3);

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        for expression in [first, second] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn patterned_intrinsic_indexes_take_precedence_and_replay_warm() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements {\n",
                "    [tag: string]: any;\n",
                "    [tag: `custom-${string}`]: { label: string };\n",
                "  }\n",
                "}\n",
                "const patterned = <custom-panel label=\"ready\" />;\n",
                "const fallback = <plain-panel optional={1} />;\n",
                "const mismatch = <custom-panel label={1} />;\n",
            ),
            FileId::new(8_128),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let patterned = fixture.expression("patterned");
        let fallback = fixture.expression("fallback");
        let mismatch = fixture.expression("mismatch");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [patterned, fallback, mismatch] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }

        let pattern_symbol = fixture
            .store
            .symbol_node_links(patterned)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        let fallback_symbol = fixture
            .store
            .symbol_node_links(fallback)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        assert_ne!(pattern_symbol, fallback_symbol);
        assert_eq!(
            fixture
                .store
                .symbol_node_links(mismatch)
                .and_then(|links| links.resolved_symbol),
            Some(pattern_symbol),
        );
        for expression in [patterned, fallback, mismatch] {
            assert_eq!(
                fixture
                    .store
                    .jsx_element_links(expression)
                    .unwrap()
                    .jsx_flags,
                JsxFlags::INTRINSIC_INDEXED_ELEMENT,
            );
        }
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        for expression in [patterned, fallback, mismatch] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                diagnostics.as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn unmatched_intrinsic_patterns_keep_the_exact_opening_diagnostic() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { [tag: `custom-${string}`]: any; }\n",
                "}\n",
                "const view = <plain-panel />;\n",
            ),
            FileId::new(8_129),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let opening = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(opening, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(diagnostics.len(), 1);
        let diagnostic = &diagnostics.as_slice()[0];
        assert_eq!(diagnostic.node, Some(opening));
        assert_eq!(diagnostic.diagnostic.code(), 2339);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Property 'plain-panel' does not exist on type 'JSX.IntrinsicElements'.",
        );
    }

    #[test]
    fn excess_jsx_attributes_report_exact_names_without_missing_property_duplicates() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { div: { label: string }; }\n",
                "}\n",
                "const first = <div extra=\"bad\" />;\n",
                "const second = <div ns:invalid=\"bad\" />;\n",
                "const missing = <div />;\n",
            ),
            FileId::new(8_130),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let missing = fixture.expression("missing");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [first, second, missing] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }

        assert_eq!(diagnostics.len(), 3);
        for (diagnostic, (expected_name, expected_source)) in
            diagnostics.as_slice().iter().take(2).zip([
                ("extra", "{ extra: string; }"),
                ("ns:invalid", "{ \"ns:invalid\": string; }"),
            ])
        {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            let anchor = diagnostic.node.unwrap();
            let record = fixture.parsed.arena.get(anchor.node).unwrap();
            let actual_name = match &record.data {
                NodeData::Identifier(name) => name.text.clone(),
                NodeData::JsxNamespacedName(name) => {
                    let NodeData::Identifier(namespace) =
                        &fixture.parsed.arena.get(name.namespace).unwrap().data
                    else {
                        unreachable!("the fixture uses an identifier namespace")
                    };
                    let NodeData::Identifier(local) =
                        &fixture.parsed.arena.get(name.name).unwrap().data
                    else {
                        unreachable!("the fixture uses an identifier local name")
                    };
                    format!("{}:{}", namespace.text, local.text)
                }
                _ => unreachable!("the diagnostic is anchored to a JSX attribute name"),
            };
            assert_eq!(actual_name, expected_name);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Type '{expected_source}' is not assignable to type '{{ label: string; }}'.\n  \
                     Property '{expected_name}' does not exist on type '{{ label: string; }}'.",
                ),
            );
        }

        let required = &diagnostics.as_slice()[2];
        assert_eq!(required.diagnostic.code(), 2741);
        assert_eq!(
            required.diagnostic.render().unwrap(),
            "Property 'label' is missing in type '{}' but required in type '{ label: string; }'.",
        );
        let NodeData::Identifier(name) = &fixture
            .parsed
            .arena
            .get(required.node.unwrap().node)
            .unwrap()
            .data
        else {
            unreachable!("the missing property diagnostic is anchored to the JSX tag")
        };
        assert_eq!(name.text, "div");

        let warm = diagnostics.as_slice().to_vec();
        for expression in [first, second, missing] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }
        assert_eq!(diagnostics.as_slice(), warm.as_slice());
    }

    #[test]
    fn namespaced_jsx_attributes_keep_their_combined_name_and_identifier_types() {
        let mut fixture = RuntimeFixture::new(
            "const view = <div ns:thing=\"ok\" />;\n",
            FileId::new(8_114),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 7026);

        let (name, namespace, local, attribute) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::JsxNamespacedName(name) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, name.namespace),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, name.name),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, record.parent?),
                ))
            })
            .unwrap();
        let symbol = fixture.bound.symbol(attribute).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();

        assert_eq!(
            fixture
                .store
                .symbol_node_links(name)
                .and_then(|links| links.resolved_symbol),
            Some(symbol),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(name)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.string_type),
        );
        for identifier in [namespace, local] {
            assert_eq!(
                fixture
                    .store
                    .type_node_links(identifier)
                    .and_then(|links| links.resolved_type),
                Some(bootstrap.error_type),
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep all upstream spread artifacts in one fixture.
    fn inline_object_spread_preserves_runtime_and_property_artifacts() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare const EntryTextDialog: any;\n",
                "const view = <EntryTextDialog {...{ ",
                "first: 0, foo: 1, bar: 2 as any, baz: 3, last: 4 ",
                "}} />;\n",
            ),
            FileId::new(8_123),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Automatic, &mut diagnostics);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2875);
        let object = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let object_type = fixture
            .store
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            type_to_string(&fixture.store, object_type).unwrap(),
            "{ first: number; foo: number; bar: any; baz: number; last: number; }",
        );

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let any = bootstrap.any_type;
        let error = bootstrap.error_type;
        let members = fixture
            .store
            .type_payload(object_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .unwrap();
        for (node, record) in fixture.parsed.arena.iter() {
            let NodeData::PropertyAssignment(property) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
            let name = NodeRef::new(fixture.parsed.arena.id(), fixture.file, property.name);
            let NodeData::Identifier(identifier) =
                &fixture.parsed.arena.get(property.name).unwrap().data
            else {
                unreachable!("the fixture uses identifier object properties")
            };
            let expected = if identifier.text == "bar" {
                any
            } else {
                number
            };
            let source_symbol = fixture.bound.symbol(declaration).unwrap();
            let cloned = fixture
                .store
                .symbol_table(members)
                .and_then(|members| members.get_source(&identifier.text))
                .unwrap();

            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol),
                Some(source_symbol),
            );
            assert_eq!(
                fixture
                    .store
                    .type_node_links(name)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
            assert_eq!(
                fixture.store.value_symbol_links(cloned),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(expected),
                    target: Some(source_symbol),
                    ..ValueSymbolLinks::default()
                }),
            );
        }

        let assertion = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::AsExpression).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        assert_eq!(
            fixture
                .store
                .type_node_links(assertion)
                .and_then(|links| links.resolved_type),
            Some(any),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(expression)
                .and_then(|links| links.resolved_type),
            Some(error),
        );
    }

    #[test]
    fn inline_object_spread_preserves_strict_property_diagnostics() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface Element {}\n",
                "  interface IntrinsicElements { div: { count: string }; }\n",
                "}\n",
                "const view = <div {...{ count: 1 }} />;\n",
            ),
            FileId::new(8_124),
        );
        let namespace = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        let anchor = diagnostics.as_slice()[0].node.unwrap();
        let NodeData::Identifier(name) = &fixture.parsed.arena.get(anchor.node).unwrap().data
        else {
            unreachable!("the object property name owns its assignment diagnostic")
        };
        assert_eq!(name.text, "count");
    }

    #[test]
    fn jsx_template_index_only_matches_compatible_attribute_names() {
        let mut fixture = RuntimeFixture::new("const view = <div />;\n", FileId::new(8_122));
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let any = bootstrap.any_type;
        let pattern = fixture
            .store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();
        let patterned = fixture
            .store
            .alloc_index_info(pattern, number, false, None, Vec::new())
            .unwrap();
        let fallback = fixture
            .store
            .alloc_index_info(string, any, false, None, Vec::new())
            .unwrap();

        assert_eq!(
            matching_attribute_index_value_type(&fixture.store, &[patterned], "do-click").unwrap(),
            Some(number),
        );
        assert_eq!(
            matching_attribute_index_value_type(&fixture.store, &[patterned], "ns:thing").unwrap(),
            None,
        );
        assert_eq!(
            matching_attribute_index_value_type(
                &fixture.store,
                &[fallback, patterned],
                "do-click",
            )
            .unwrap(),
            Some(number),
        );
        assert_eq!(
            matching_attribute_index_value_type(
                &fixture.store,
                &[fallback, patterned],
                "ns:thing",
            )
            .unwrap(),
            Some(any),
        );
    }

    #[test]
    fn unpublished_arrow_component_is_unsupported_instead_of_a_call_invariant() {
        let fixture = RuntimeFixture::new(
            concat!(
                "const Title = (props: { children: string }) => <h1>{props.children}</h1>;\n",
                "const element = <Title>Hello, world!</Title>;\n",
            ),
            FileId::new(8_133),
        );
        let component = resolve_source_value_symbol(&fixture.store, &fixture.bound, "Title")
            .expect("the component declaration must be bound");
        let initializer = fixture.expression("Title");
        let expression = fixture.expression("element");
        let NodeData::JsxElement(element) =
            &fixture.parsed.arena.get(expression.node).unwrap().data
        else {
            unreachable!("the source contains a paired component")
        };
        let opening = child_ref(expression, element.opening_element);
        let NodeData::JsxOpeningElement(element) =
            &fixture.parsed.arena.get(opening.node).unwrap().data
        else {
            unreachable!("the paired component has an opening element")
        };
        let tag = child_ref(opening, element.tag_name);

        let result = jsx_component_value_type(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            component,
            tag,
        );

        assert!(matches!(
            result,
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node,
                    kind: SyntaxKind::ArrowFunction,
                    role: SourceSyntaxRole::VariableInitializer,
                }
            )) if node == initializer
        ));
    }

    #[test]
    fn ambient_component_reads_its_staged_annotation_without_publishing_value_links() {
        let mut fixture = RuntimeFixture::new(
            "declare var Fragment: any;\nconst view = <Fragment></Fragment>;\n",
            FileId::new(8_115),
        );
        let expression = fixture.expression("view");
        let (declaration, annotation) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (name.text == "Fragment").then_some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, variable.type_?),
                ))
            })
            .unwrap();
        let symbol = fixture.bound.symbol(declaration).unwrap();
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert!(fixture.store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(any),
                ..TypeNodeLinks::default()
            },
        ));

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert!(diagnostics.is_empty());
        assert!(fixture.store.value_symbol_links(symbol).is_none());
        let NodeData::JsxElement(element) =
            &fixture.parsed.arena.get(expression.node).unwrap().data
        else {
            unreachable!("the fixture contains an opening and closing component")
        };
        let NodeData::JsxOpeningElement(opening) = &fixture
            .parsed
            .arena
            .get(element.opening_element)
            .unwrap()
            .data
        else {
            unreachable!("the fixture contains an opening component")
        };
        let NodeData::JsxClosingElement(closing) = &fixture
            .parsed
            .arena
            .get(element.closing_element)
            .unwrap()
            .data
        else {
            unreachable!("the fixture contains a closing component")
        };
        for name in [opening.tag_name, closing.tag_name] {
            let name = NodeRef::new(expression.arena, expression.file, name);
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol),
                Some(symbol),
            );
            assert_eq!(
                fixture
                    .store
                    .type_node_links(name)
                    .and_then(|links| links.resolved_type),
                Some(any),
            );
        }
    }

    #[test]
    fn ambient_component_resolves_an_uncached_annotation_without_publishing_it() {
        let mut fixture = RuntimeFixture::new(
            "declare var Fragment: any;\nconst view = <Fragment></Fragment>;\n",
            FileId::new(8_116),
        );
        let expression = fixture.expression("view");
        let (declaration, annotation) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (name.text == "Fragment").then_some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, variable.type_?),
                ))
            })
            .unwrap();
        let symbol = fixture.bound.symbol(declaration).unwrap();

        assert!(fixture.store.type_node_links(annotation).is_none());
        assert!(fixture.store.value_symbol_links(symbol).is_none());

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert!(diagnostics.is_empty());
        assert!(fixture.store.type_node_links(annotation).is_none());
        assert!(fixture.store.value_symbol_links(symbol).is_none());
    }

    #[test]
    fn source_check_accepts_ambient_component_before_value_publication() {
        let source = concat!(
            "/** @jsx h */\n",
            "declare var h: any;\n",
            "declare var Fragment: any;\n",
            "declare namespace JSX { interface Element {} }\n",
            "const view = <Fragment></Fragment>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_117);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/pragma.tsx\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = crate::semantic::CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn classic_runtime_forces_lazy_ambient_function_component_returns() {
        for (index, namespace_member) in ["ElementType", "LibraryManagedAttributes"]
            .into_iter()
            .enumerate()
        {
            let source = format!(
                "declare namespace JSX {{ enum {namespace_member} {{}} }}\n\
                 declare const C: () => any;\n\
                 const view = <C />;\n"
            );
            let parsed = parse_jsx_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_118 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/component.tsx\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let mut context = crate::semantic::CanonicalCheckerContext::new(
                binder.finish(),
                vec![(file, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();

            context
                .check_source_file_with_jsx_runtime(
                    file,
                    CanonicalJsxRuntimeEvidence::Classic {
                        factory_namespace: "React",
                        fragment_factory_namespace: "React",
                        fragment_factory_required: false,
                        fragment_factory_pragma_required: false,
                    },
                )
                .unwrap();

            assert_eq!(context.diagnostics().len(), 1);
            assert_eq!(context.diagnostics().as_slice()[0].diagnostic.code(), 2874);
        }
    }

    #[test]
    fn jsx_children_accept_parenthesized_conditional_elements() {
        let mut fixture = RuntimeFixture::new(
            "const view = <div>{0 ? (<span />) : (<section />)}</div>;\n",
            FileId::new(8_120),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [7026, 7026, 7026, 7026],
        );
        let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        for (node, record) in fixture.parsed.arena.iter() {
            if matches!(
                record.kind,
                SyntaxKind::ConditionalExpression | SyntaxKind::ParenthesizedExpression
            ) {
                let node = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                assert_eq!(
                    fixture
                        .store
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type),
                    Some(error),
                );
            }
        }
    }

    #[test]
    fn jsx_children_read_cached_initializers_before_value_publication() {
        let mut fixture = RuntimeFixture::new(
            "const saved = 1 as any;\nconst view = <div>{saved}</div>;\n",
            FileId::new(8_121),
        );
        let expression = fixture.expression("view");
        let initializer = fixture.expression("saved");
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert!(fixture.store.set_type_node_links(
            initializer,
            TypeNodeLinks {
                resolved_type: Some(any),
                ..TypeNodeLinks::default()
            },
        ));

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(diagnostics.len(), 2);
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 7026)
        );
        let reference = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                (identifier.text == "saved"
                    && record
                        .parent
                        .and_then(|parent| fixture.parsed.arena.get(parent))
                        .is_some_and(|parent| parent.kind == SyntaxKind::JsxExpression))
                .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap();
        assert_eq!(
            fixture
                .store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(any),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source proves scoped reads and warm child-attribute state.
    fn automatic_runtime_uses_scoped_property_reads_and_implicit_children() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface IntrinsicElements { h1: { children: string }; }\n",
            "  type Element = string;\n",
            "}\n",
            "const Title = (props: { children: string }) => <h1>{props.children}</h1>;\n",
            "const element = <Title>Hello, world!</Title>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_131);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/automatic-children.tsx\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = crate::semantic::CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                jsx_runtime: CanonicalJsxRuntime::Automatic,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let module = context
            .store_mut_for_test()
            .alloc_symbol(SymbolData::new(
                SymbolFlags::VALUE_MODULE,
                EscapedName::source("\"/jsx/jsx-runtime\""),
            ))
            .unwrap();
        let runtime = CanonicalJsxRuntimeEvidence::Automatic {
            module_specifier: "/jsx/jsx-runtime",
            resolved_module: Some(module),
        };

        context
            .check_source_file_with_jsx_runtime(file, runtime)
            .unwrap();

        assert!(context.diagnostics().is_empty());
        let access = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            unreachable!("the source contains one parameter property read")
        };
        let receiver = child_ref(access, property.expression);
        let name = child_ref(access, property.name);
        let parameter = context
            .store()
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        let member = context
            .store()
            .symbol_node_links(access)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        assert_eq!(
            context.store().symbol(parameter).unwrap().name().as_utf8(),
            Some("props"),
        );
        assert_eq!(
            context.store().symbol(member).unwrap().name().as_utf8(),
            Some("children"),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(name)
                .and_then(|links| links.resolved_symbol),
            Some(member),
        );
        let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string_type),
        );

        let children_properties = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::JsxAttributes).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .map(|attributes| {
                let type_ = context
                    .store()
                    .type_node_links(attributes)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let members = context
                    .store()
                    .type_payload(type_)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.members)
                    .and_then(|members| context.store().symbol_table(members))
                    .unwrap();
                let children = members.get_source("children").unwrap();
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(children)
                        .and_then(|links| links.resolved_type),
                    Some(string_type),
                );
                children
            })
            .collect::<Vec<_>>();
        assert_eq!(children_properties.len(), 2);
        assert_ne!(children_properties[0], children_properties[1]);

        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            cold,
        );
    }

    #[test]
    fn automatic_runtime_ignores_the_declared_children_attribute_name() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface IntrinsicElements { h1: { children: string }; }\n",
            "  type Element = string;\n",
            "  interface ElementChildrenAttribute { offspring: any; }\n",
            "}\n",
            "const Title = (props: { children: string }) => <h1>{props.children}</h1>;\n",
            "const valid = <Title>Hello, world!</Title>;\n",
            "const Wrong = (props: { offspring: string }) => <h1>{props.offspring}</h1>;\n",
            "const invalid = <Wrong>Byebye, world!</Wrong>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_132);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/automatic-child-name.tsx\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = crate::semantic::CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let module = context
            .store_mut_for_test()
            .alloc_symbol(SymbolData::new(
                SymbolFlags::VALUE_MODULE,
                EscapedName::source("\"/jsx/jsx-runtime\""),
            ))
            .unwrap();

        context
            .check_source_file_with_jsx_runtime(
                file,
                CanonicalJsxRuntimeEvidence::Automatic {
                    module_specifier: "/jsx/jsx-runtime",
                    resolved_module: Some(module),
                },
            )
            .unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("automatic JSX must report only the missing offspring property")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2741);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Property 'offspring' is missing in type '{ children: string; }' \
             but required in type '{ offspring: string; }'.",
        );
        let NodeData::Identifier(tag) = &parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .data
        else {
            unreachable!("the missing property belongs to the component tag")
        };
        assert_eq!(tag.text, "Wrong");
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the missing property must point to its declaration")
        };
        assert_eq!(related.diagnostic.code(), 2728);
        let NodeData::Identifier(declaration) =
            &parsed.arena.get(related.node.unwrap().node).unwrap().data
        else {
            unreachable!("the related location belongs to the declared property")
        };
        assert_eq!(declaration.text, "offspring");
    }

    #[test]
    fn automatic_runtime_preserves_the_exact_custom_missing_module() {
        let mut fixture = RuntimeFixture::new("const app = <App />;\n", FileId::new(8_105));
        let expression = fixture.expression("app");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        fixture.check_with_evidence(
            expression,
            CanonicalJsxRuntime::Automatic,
            CanonicalJsxRuntimeEvidence::Automatic {
                module_specifier: "preact/jsx-runtime",
                resolved_module: None,
            },
            &mut diagnostics,
        );

        let runtime = diagnostics
            .as_slice()
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == 2875)
            .unwrap();
        assert_eq!(
            runtime.diagnostic.render().unwrap(),
            "This JSX tag requires the module path 'preact/jsx-runtime' to exist, but none could be found. Make sure you have types for the appropriate package installed.",
        );
    }

    #[test]
    fn automatic_runtime_anchors_a_missing_module_to_the_opening_fragment() {
        let fixture = RuntimeFixture::new("const view = <><span /></>;\n", FileId::new(8_107));
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Automatic {
                module_specifier: "preact/jsx-runtime",
                resolved_module: None,
            },
        )
        .unwrap();

        let diagnostic = diagnostics.as_slice().first().unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostic.diagnostic.code(), 2875);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::JsxOpeningFragment,
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This JSX tag requires the module path 'preact/jsx-runtime' to exist, but none could be found. Make sure you have types for the appropriate package installed.",
        );
    }

    #[test]
    fn automatic_runtime_does_not_diagnose_a_proven_module() {
        let mut fixture = RuntimeFixture::new("const app = <App />;\n", FileId::new(8_106));
        let module = fixture
            .store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::VALUE_MODULE,
                EscapedName::source("\"preact/jsx-runtime\""),
            ))
            .unwrap();
        let snapshot = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture
                .store
                .jsx_element_links(fixture.bound.source_file())
                .cloned(),
        );
        let diagnostics = source_jsx_runtime_diagnostics(
            &fixture.store,
            &fixture.parsed.arena,
            &fixture.bound,
            CanonicalJsxRuntimeEvidence::Automatic {
                module_specifier: "preact/jsx-runtime",
                resolved_module: Some(module),
            },
        )
        .unwrap();

        assert!(diagnostics.is_empty());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture
                    .store
                    .jsx_element_links(fixture.bound.source_file())
                    .cloned(),
            ),
            snapshot,
        );
    }
}
