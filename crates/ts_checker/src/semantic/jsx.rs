//! Canonical checking for basic JSX elements.
//!
//! This module follows the pinned JSX checker for global `JSX` namespaces,
//! named or indexed intrinsic tags, and fixed function components. It writes
//! only to the existing semantic graph. Spread attributes, generic components,
//! dotted component names, contextual children, and factory imports remain
//! explicit source-capability boundaries.

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
    formatter::{get_type_names_for_assignability_error, type_to_string},
    production::CanonicalJsxRuntimeEvidence,
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
        attributes: Vec<JsxAttributePlan>,
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
enum JsxAttributeValue {
    ImplicitTrue,
    Expression {
        wrapper: Option<NodeRef>,
        value: JsxScalarPlan,
    },
}

#[derive(Clone, Debug)]
enum JsxScalarPlan {
    String { node: NodeRef, value: String },
    Number { node: NodeRef, value: Number },
    Boolean { node: NodeRef, value: bool },
    Null(NodeRef),
    Identifier { node: NodeRef, name: String },
    Element(Box<JsxElementPlan>),
}

#[derive(Clone, Debug)]
enum JsxChildPlan {
    Text,
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
    /// rejects unsupported tags, spreads, malformed binder ownership, and
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
    /// `JSX.Element` and `JSX.IntrinsicElements` are resolved through existing
    /// declaration queries. Intrinsic tags retain their upstream symbol,
    /// signature, attribute, and JSX links. Function components reuse their
    /// existing fixed call signature. Unsupported syntax returns a typed
    /// source boundary instead of inventing an `any` result.
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
        let namespace = resolve_jsx_namespace(self, host, options, diagnostics, expression)?;
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
) -> Result<Vec<JsxAttributePlan>, SourceCheckError> {
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
        .collect()
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
                    result.push(JsxChildPlan::Text);
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
    location: NodeRef,
) -> Result<JsxNamespace, SourceCheckError> {
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
            element_type = resolve_namespace_export_type(
                store,
                host,
                namespace,
                symbol,
                options,
                diagnostics,
            )?;
        }
        if let Some(symbol) = intrinsic {
            if store
                .symbol(symbol)
                .is_none_or(|record| !record.flags().intersects(SymbolFlags::TYPE))
            {
                return Err(SourceCheckError::Property(location));
            }
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

    Ok(JsxNamespace {
        element_type,
        intrinsic_elements,
        unknown_symbol,
        error_type,
        any_type,
    })
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
                let name_record = host
                    .node(name_node)
                    .ok_or(SourceCheckError::Property(name_node))?;
                let name = match &name_record.data {
                    NodeData::Identifier(name) if name_record.kind == SyntaxKind::Identifier => {
                        name.text.as_str()
                    }
                    NodeData::StringLiteral(name)
                        if name_record.kind == SyntaxKind::StringLiteral =>
                    {
                        name.text.as_str()
                    }
                    _ => return Err(unsupported(name_node, name_record.kind)),
                };
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
                    || property_record.name().as_utf8() != Some(name)
                    || property_record.parent() != Some(symbol)
                    || members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get_source(name))
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
                publish_type_links(store, tag.node, namespace.any_type)?;
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
                    arena,
                    bound,
                    namespace,
                    plan.opening,
                    tag,
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
            let checked = check_jsx_attributes(
                store,
                (arena, bound),
                namespace,
                expected_attributes,
                attributes,
                options,
                diagnostics,
            )?;
            let actual_attributes =
                publish_attribute_object(store, bound, *attributes_node, &checked)?;
            check_attribute_assignability(
                store,
                plan.opening,
                tag,
                expected_attributes,
                actual_attributes,
                &checked,
                diagnostics,
            )?;
        }
    }

    for child in &plan.children {
        match child {
            JsxChildPlan::Text => {}
            JsxChildPlan::Expression { wrapper, value } => {
                let type_ =
                    execute_scalar(store, arena, bound, namespace, value, options, diagnostics)?;
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

    publish_type_links(store, plan.expression, namespace.element_type)?;
    Ok(namespace.element_type)
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
        publish_type_links(store, closing.tag.node, namespace.any_type)?;
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
    for index in indexes {
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
        if key_type != string_type {
            continue;
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
    arena: &NodeArena,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    opening: NodeRef,
    tag: &JsxTagPlan,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(TypeId, SignatureId), SourceCheckError> {
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
        || callable.return_type.is_none()
    {
        return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
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
    if variable.initializer.is_some() {
        return Err(SourceCheckError::Call(location));
    }
    let annotation = variable
        .type_
        .map(|annotation| child_ref(declaration, annotation))
        .ok_or(SourceCheckError::Call(location))?;
    let annotation_record = jsx_node(arena, bound, store, annotation)?;
    if annotation_record.parent != Some(declaration.node) {
        return Err(SourceCheckError::Call(location));
    }
    store
        .type_node_links(annotation)
        .and_then(|links| links.resolved_type)
        .filter(|type_| store.type_payload(*type_).is_some())
        .ok_or(SourceCheckError::Call(location))
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
            let Some(symbol) = resolve_source_value_symbol(store, bound, name) else {
                add_diagnostic(diagnostics, *node, 2304, [name.as_str()])?;
                publish_type_links(store, *node, namespace.error_type)?;
                return Ok(namespace.error_type);
            };
            let type_ = store
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .ok_or(SourceCheckError::Property(*node))?;
            publish_symbol_links(store, *node, symbol)?;
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
        validate_attribute_object(store, type_, owner, attributes, attributes_node)?;
        return Ok(type_);
    }
    if !store.try_reserve_checker_symbol_allocations(attributes.len(), 1)
        || !store.try_reserve_value_symbol_links(attributes.len())
        || !store.try_reserve_types(1)
        || !store.try_reserve_type_node_links(1)
    {
        return Err(SourceCheckError::Property(attributes_node));
    }
    let members = store.alloc_symbol_table();
    let mut properties = Vec::with_capacity(attributes.len());
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
    if structured.properties.as_deref().unwrap_or_default().len() != attributes.len() {
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
    Ok(())
}

fn check_attribute_assignability(
    store: &mut CanonicalTypeMapperStore,
    opening: NodeRef,
    tag: &JsxTagPlan,
    expected: TypeId,
    actual: TypeId,
    attributes: &[CheckedJsxAttribute],
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
        } else if let Some(type_) = string_index_value_type(store, &index_infos)? {
            type_
        } else if attribute.plan.name.contains('-') {
            continue;
        } else {
            let target = type_to_string(store, expected)?;
            let detail = Diagnostic::with_arguments(
                message_by_code(2339).ok_or(SourceCheckError::MissingDiagnostic(2339))?,
                [attribute.plan.name.as_str(), target.as_str()],
            )
            .render()
            .map_err(|_| SourceCheckError::MissingDiagnostic(2339))?;
            let diagnostic = Diagnostic::with_arguments(
                message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                [format_attribute_object(attributes), target],
            )
            .with_details([format!("  {detail}")]);
            merge_retry_diagnostic(
                diagnostics,
                CanonicalCheckerDiagnostic {
                    node: Some(tag.node),
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
            let source = if attributes.is_empty() {
                "{}".to_owned()
            } else {
                format_attribute_object(attributes)
            };
            let target = type_to_string(store, expected)?;
            add_diagnostic(diagnostics, tag.node, 2741, [name, &source, &target])?;
        }
    }

    if store.type_payload(actual).is_none() {
        return Err(SourceCheckError::Property(opening));
    }
    Ok(())
}

fn string_index_value_type(
    store: &CanonicalTypeMapperStore,
    indexes: &[super::IndexInfoId],
) -> Result<Option<TypeId>, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    for index in indexes {
        let Some(info) = store.index_info(*index) else {
            return Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::Capacity,
            ));
        };
        if info.key_type() == bootstrap.string_type {
            return Ok(Some(info.value_type()));
        }
    }
    Ok(None)
}

fn format_attribute_object(attributes: &[CheckedJsxAttribute]) -> String {
    if attributes.is_empty() {
        return "{}".to_owned();
    }
    let names = attributes
        .iter()
        .map(|attribute| format!("{}: unknown;", attribute.plan.name))
        .collect::<Vec<_>>()
        .join(" ");
    format!("{{ {names} }}")
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
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_jsx_source_file};

    use super::*;
    use crate::semantic::{IntrinsicBootstrapOptions, production::CanonicalJsxRuntime};

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
