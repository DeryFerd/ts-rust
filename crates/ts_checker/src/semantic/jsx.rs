//! Canonical checking for basic JSX elements.
//!
//! This module follows the pinned JSX checker for global `JSX` namespaces,
//! named or indexed intrinsic tags, and fixed or inferred function components.
//! It writes only to the existing semantic graph. Inline object-literal and
//! identifier spreads reuse canonical object publication. Dotted component
//! names retain authenticated namespace exports. Other spreads, broader
//! contextual child expressions, and factory imports remain explicit boundaries.

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
    CanonicalCheckerOptions, CanonicalCheckerRelatedInformation, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeHost, DeclaredTypeLinks, JsxElementLinks, JsxFlags,
    ResolvedSignatureState, SignatureId, SignatureLinks, SourceCheckError,
    SourceCheckProvenanceError, SourceLiteralCacheError, SourceSyntaxRole, SymbolNodeLinks, TypeId,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    formatter::{
        CanonicalTypeFormatFlags, get_type_names_for_assignability_error,
        type_to_string_with_host_and_flags,
    },
    indexed_access_types::template_pattern_index_matches_name,
    instantiate::{InstantiationLimits, InstantiationSession},
    instantiated_members::{demand_instantiated_property_type, resolve_members_with_array_targets},
    mapped_types::MappedTypeModifiers,
    production::{CanonicalJsxRuntime, CanonicalJsxRuntimeEvidence},
    reference_types::{create_direct_generic_reference, validate_direct_generic_reference},
    signatures::SignatureFlags,
    source::merge_retry_diagnostic,
    source_calls::resolve_jsx_generic_component_signature,
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
    namespace_member: Option<JsxNamespaceMemberPlan>,
}

#[derive(Clone, Debug)]
struct JsxNamespaceMemberPlan {
    namespace: SemanticSymbolId,
    namespace_node: NodeRef,
    member: SemanticSymbolId,
    member_node: NodeRef,
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
    SourceSpread(Box<JsxSourceSpreadPlan>),
}

#[derive(Clone, Debug)]
struct JsxObjectSpreadPlan {
    node: NodeRef,
    object: super::object_members::PropertyObjectPlan,
    properties: Vec<JsxAttributePlan>,
}

#[derive(Clone, Debug)]
struct JsxSourceSpreadPlan {
    node: NodeRef,
    value: JsxScalarPlan,
}

#[derive(Clone, Debug)]
enum JsxAttributeValue {
    ImplicitTrue,
    EmptyExpression {
        wrapper: NodeRef,
        report: bool,
    },
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
    GlobalThis(NodeRef),
    Property {
        node: NodeRef,
        receiver: Box<Self>,
        name_node: NodeRef,
        name: String,
    },
    TypeAssertion {
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
    AdjacentElements {
        node: NodeRef,
        left: Box<JsxElementPlan>,
        right: Box<JsxElementPlan>,
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
    element_type_constraint: Option<TypeId>,
    intrinsic_elements: Option<TypeId>,
    children_attribute: Option<SemanticSymbolId>,
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
    name: Option<SemanticSymbolId>,
    individual_errors: bool,
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

#[derive(Clone, Copy, Debug)]
struct JsxRecordHeritage {
    node: NodeRef,
    alias: SemanticSymbolId,
}

#[derive(Clone, Copy, Debug)]
struct DeferredReactAttributeProperty {
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    type_argument: Option<TypeId>,
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
        self.check_jsx_element_inner(host, None, expression, options, diagnostics)
    }

    pub(super) fn check_jsx_element_with_global_types(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        global_types: &CanonicalGlobalTypes,
        expression: NodeRef,
        options: CanonicalCheckerOptions,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, SourceCheckError> {
        self.check_jsx_element_inner(host, Some(global_types), expression, options, diagnostics)
    }

    fn check_jsx_element_inner(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        global_types: Option<&CanonicalGlobalTypes>,
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
        execute_jsx_element(
            self,
            (arena, bound, host, global_types),
            &namespace,
            &plan,
            options,
            diagnostics,
        )
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
            let closing = if recovered_conflict_marker_closing(
                arena,
                bound,
                store,
                expression,
                closing_node,
                closing_data.tag_name,
            )? {
                None
            } else {
                Some(JsxClosingPlan {
                    node: closing_node,
                    tag: plan_jsx_tag(arena, bound, store, closing_node, closing_data.tag_name)?,
                })
            };
            Ok(JsxElementPlan {
                expression,
                opening,
                kind: JsxElementPlanKind::Element {
                    tag,
                    attributes_node,
                    attributes,
                    type_arguments,
                    closing,
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

fn recovered_conflict_marker_closing(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    expression: NodeRef,
    closing: NodeRef,
    name: ts_ast::NodeId,
) -> Result<bool, SourceCheckError> {
    let name = child_ref(closing, name);
    let record = jsx_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Ok(false);
    };
    if !identifier.text.is_empty() {
        return Ok(false);
    }
    let closing_record = jsx_node(arena, bound, store, closing)?;
    let expression_record = jsx_node(arena, bound, store, expression)?;
    let marker = arena
        .source_text()
        .and_then(|source| source.get(record.range.start.get() as usize..))
        .is_some_and(|source| {
            source
                .strip_prefix("\r\n")
                .or_else(|| source.strip_prefix('\n'))
                .unwrap_or(source)
                .starts_with("<<<<<<<")
        });
    let recovered_unary = recovered_javascript_unary_plus_closing(
        arena,
        bound,
        store,
        expression,
        record.range.start,
    )?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 1 << 15
        || identifier.flow_node.is_some()
        || record.parent != Some(closing.node)
        || record.range.start != record.range.end
        || closing_record.flags.0 != 0
        || closing_record.range != record.range
        || expression_record.range.end != closing_record.range.end
        || !marker && !recovered_unary
    {
        return Err(unsupported(name, record.kind));
    }
    Ok(true)
}

fn recovered_javascript_unary_plus_closing(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    expression: NodeRef,
    position: ts_core::TextPos,
) -> Result<bool, SourceCheckError> {
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
        || arena
            .source_text()
            .and_then(|source| source.get(position.get() as usize..))
            .is_none_or(|suffix| !suffix.trim().is_empty())
    {
        return Ok(false);
    }
    let record = jsx_node(arena, bound, store, expression)?;
    let NodeData::JsxElement(element) = &record.data else {
        return Ok(false);
    };
    let opening = child_ref(expression, element.opening_element);
    let opening_record = jsx_node(arena, bound, store, opening)?;
    let NodeData::JsxOpeningElement(opening_data) = &opening_record.data else {
        return Ok(false);
    };
    let tag = child_ref(opening, opening_data.tag_name);
    let tag_record = jsx_node(arena, bound, store, tag)?;
    if !matches!(&tag_record.data, NodeData::Identifier(name) if name.text == "number") {
        return Ok(false);
    }
    let Some(parent) = record.parent.map(|parent| child_ref(expression, parent)) else {
        return Ok(false);
    };
    let parent_record = jsx_node(arena, bound, store, parent)?;
    let NodeData::PrefixUnaryExpression(prefix) = &parent_record.data else {
        return Ok(false);
    };
    if parent_record.kind != SyntaxKind::PrefixUnaryExpression
        || parent_record.flags.0 != 0
        || prefix.operator != SyntaxKind::PlusToken
        || prefix.operand != expression.node
    {
        return Ok(false);
    }
    let Some(variable) = parent_record.parent.map(|node| child_ref(parent, node)) else {
        return Ok(false);
    };
    let variable_record = jsx_node(arena, bound, store, variable)?;
    Ok(matches!(
        &variable_record.data,
        NodeData::VariableDeclaration(declaration)
            if variable_record.kind == SyntaxKind::VariableDeclaration
                && declaration.type_.is_none()
                && declaration.initializer == Some(parent.node)
    ))
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
                namespace_member: None,
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
                namespace_member: None,
            })
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.question_dot_token.is_none()
                && access.flow_node.is_none()
                && access.facts == 0 =>
        {
            let namespace_node = child_ref(node, access.expression);
            let member_node = child_ref(node, access.name);
            let namespace_record = jsx_node(arena, bound, store, namespace_node)?;
            let member_record = jsx_node(arena, bound, store, member_node)?;
            let (NodeData::Identifier(namespace_name), NodeData::Identifier(member_name)) =
                (&namespace_record.data, &member_record.data)
            else {
                return Err(unsupported(node, record.kind));
            };
            if namespace_record.kind != SyntaxKind::Identifier
                || namespace_record.flags.0 != 0
                || namespace_record.parent != Some(node.node)
                || namespace_name.flow_node.is_some()
                || namespace_name.text.is_empty()
                || member_record.kind != SyntaxKind::Identifier
                || member_record.flags.0 != 0
                || member_record.parent != Some(node.node)
                || member_name.flow_node.is_some()
                || member_name.text.is_empty()
            {
                return Err(unsupported(node, record.kind));
            }
            let namespace = resolve_scoped_jsx_namespace_symbol(
                store,
                arena,
                bound,
                namespace_node,
                &namespace_name.text,
            )?
            .ok_or_else(|| unsupported(namespace_node, namespace_record.kind))?;
            let owner = store
                .symbol(namespace)
                .ok_or(SourceCheckError::Property(namespace_node))?;
            let member = owner
                .exports()
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&member_name.text))
                .and_then(|member| store.get_merged_symbol(member))
                .ok_or_else(|| unsupported(member_node, member_record.kind))?;
            let value = store
                .symbol(member)
                .ok_or(SourceCheckError::Property(member_node))?;
            if !owner.flags().intersects(SymbolFlags::MODULE)
                || !value.flags().intersects(SymbolFlags::VALUE)
                || value.check_flags() != CheckFlags::NONE
                || value.name().as_utf8() != Some(member_name.text.as_str())
                || store.get_parent_of_symbol(member) != Some(namespace)
                || value.value_declaration().is_none()
                || value
                    .declarations()
                    .is_none_or(|declarations| declarations.is_empty())
            {
                return Err(SourceCheckError::Property(member_node));
            }
            Ok(JsxTagPlan {
                node,
                name: format!("{}.{}", namespace_name.text, member_name.text),
                intrinsic: false,
                namespace_member: Some(JsxNamespaceMemberPlan {
                    namespace,
                    namespace_node,
                    member,
                    member_node,
                }),
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
        if let NodeData::JsxSpreadAttribute(spread) = &record.data {
            let expression = child_ref(node, spread.expression);
            let expression_record = jsx_node(arena, bound, store, expression)?;
            return if expression_record.kind == SyntaxKind::Identifier {
                plan_jsx_source_spread(arena, bound, store, attributes_node, node)
                    .map(|spread| JsxAttributesPlan::SourceSpread(Box::new(spread)))
            } else {
                plan_jsx_object_spread(arena, bound, store, attributes_node, node)
                    .map(|spread| JsxAttributesPlan::ObjectSpread(Box::new(spread)))
            };
        }
    }

    let mut reported_empty_expression = false;
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
                        if let Some(inner) = expression.expression {
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
                            let report = !reported_empty_expression;
                            reported_empty_expression = true;
                            JsxAttributeValue::EmptyExpression {
                                wrapper: initializer,
                                report,
                            }
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

fn plan_jsx_source_spread(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    attributes: NodeRef,
    node: NodeRef,
) -> Result<JsxSourceSpreadPlan, SourceCheckError> {
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
    let value = plan_scalar(
        arena,
        bound,
        store,
        node,
        child_ref(node, spread.expression),
    )?;
    if !matches!(&value, JsxScalarPlan::Identifier { .. }) {
        return Err(unsupported(node, SyntaxKind::JsxSpreadAttribute));
    }
    Ok(JsxSourceSpreadPlan { node, value })
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
        NodeData::KeywordExpression(keyword)
            if record.kind == SyntaxKind::ThisKeyword && keyword.flow_node.is_none() =>
        {
            if !jsx_is_script_level_this(arena, bound, node) {
                return Err(unsupported(node, record.kind));
            }
            Ok(JsxScalarPlan::GlobalThis(node))
        }
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
        {
            Ok(JsxScalarPlan::Identifier {
                node,
                name: identifier.text.clone(),
            })
        }
        NodeData::BinaryExpression(_) if record.kind == SyntaxKind::BinaryExpression => {
            plan_adjacent_jsx_attribute_elements(arena, bound, store, parent, node)
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.question_dot_token.is_none()
                && access.flow_node.is_none()
                && access.facts == 0 =>
        {
            let receiver_node = child_ref(node, access.expression);
            let receiver_record = jsx_node(arena, bound, store, receiver_node)?;
            let receiver = plan_scalar(arena, bound, store, node, receiver_node)?;
            if !matches!(&receiver, JsxScalarPlan::Identifier { .. })
                && !jsx_scalar_is_script_global_this(&receiver)
            {
                return Err(unsupported(receiver_node, receiver_record.kind));
            }
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
            if !matches!(
                type_record.kind,
                SyntaxKind::AnyKeyword | SyntaxKind::UnknownKeyword
            ) || !matches!(&type_record.data, NodeData::KeywordTypeNode(_))
                || type_record.parent != Some(node.node)
            {
                return Err(unsupported(type_node, type_record.kind));
            }
            Ok(JsxScalarPlan::TypeAssertion {
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

fn jsx_is_script_level_this(arena: &NodeArena, bound: &BoundFile, node: NodeRef) -> bool {
    if bound
        .source_facts()
        .is_none_or(ts_binder::CanonicalSourceFileFacts::is_external_or_common_js_module)
    {
        return false;
    }
    let mut parent = arena.get(node.node).and_then(|record| record.parent);
    while let Some(current) = parent {
        let Some(record) = arena.get(current) else {
            return false;
        };
        if matches!(
            record.kind,
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::Constructor
                | SyntaxKind::ClassDeclaration
                | SyntaxKind::ModuleDeclaration
        ) {
            return false;
        }
        parent = record.parent;
    }
    true
}

fn jsx_scalar_is_script_global_this(scalar: &JsxScalarPlan) -> bool {
    match scalar {
        JsxScalarPlan::GlobalThis(_) => true,
        JsxScalarPlan::Property { receiver, .. } => jsx_scalar_is_script_global_this(receiver),
        _ => false,
    }
}

fn plan_adjacent_jsx_attribute_elements(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    parent: NodeRef,
    node: NodeRef,
) -> Result<JsxScalarPlan, SourceCheckError> {
    let record = jsx_node(arena, bound, store, node)?;
    let NodeData::BinaryExpression(binary) = &record.data else {
        return Err(unsupported(node, record.kind));
    };
    let parent_record = jsx_node(arena, bound, store, parent)?;
    if binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.modifiers.is_some()
        || binary.facts != 0
        || !matches!(
            &parent_record.data,
            NodeData::JsxAttribute(attribute) if attribute.initializer == Some(node.node)
        )
    {
        return Err(unsupported(node, record.kind));
    }
    let left = child_ref(node, binary.left);
    let right = child_ref(node, binary.right);
    let comma = child_ref(node, binary.operator_token);
    let left_record = jsx_node(arena, bound, store, left)?;
    let right_record = jsx_node(arena, bound, store, right)?;
    let comma_record = jsx_node(arena, bound, store, comma)?;
    let adjacent = arena
        .source_text()
        .and_then(|source| {
            source
                .get(left_record.range.end.get() as usize..right_record.range.start.get() as usize)
        })
        .is_some_and(|source| source.trim().is_empty());
    if left_record.parent != Some(node.node)
        || right_record.parent != Some(node.node)
        || comma_record.kind != SyntaxKind::CommaToken
        || !matches!(&comma_record.data, NodeData::Token(_))
        || comma_record.parent != Some(node.node)
        || comma_record.flags.0 != 0
        || comma_record.range.start != comma_record.range.end
        || comma_record.range.start != right_record.range.start
        || left_record.range.start != record.range.start
        || right_record.range.end != record.range.end
        || !matches!(
            &left_record.data,
            NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_)
        )
        || !matches!(
            &right_record.data,
            NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_)
        )
        || !adjacent
    {
        return Err(unsupported(node, record.kind));
    }
    Ok(JsxScalarPlan::AdjacentElements {
        node,
        left: Box::new(plan_jsx_element(arena, bound, store, left)?),
        right: Box::new(plan_jsx_element(arena, bound, store, right)?),
    })
}

fn resolve_jsx_namespace(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &JsxElementPlan,
) -> Result<JsxNamespace, SourceCheckError> {
    let location = plan.expression;
    let intrinsic_names = jsx_plan_intrinsic_names(plan);
    let needs_intrinsics = !intrinsic_names.is_empty();
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
    let namespace = resolve_local_jsx_namespace(store, host, location)?.or_else(|| {
        store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("JSX"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .filter(|symbol| {
                store
                    .symbol(*symbol)
                    .is_some_and(|record| record.flags().intersects(SymbolFlags::NAMESPACE))
            })
    });

    let mut element_type = error_type;
    let mut element_type_constraint = None;
    let mut intrinsic_elements = None;
    let mut children_attribute = None;
    if let Some(namespace) = namespace {
        let exports = store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .ok_or(SourceCheckError::Property(location))?;
        let table = store
            .symbol_table(exports)
            .ok_or(SourceCheckError::Property(location))?;
        let element = table.get_source("Element");
        let element_type_symbol = table.get_source("ElementType");
        let intrinsic = table.get_source("IntrinsicElements");
        let children = table.get_source("ElementChildrenAttribute");
        if let Some(symbol) = element {
            validate_jsx_namespace_type_symbol(store, symbol, location)?;
            element_type = resolve_jsx_namespace_element_type(
                store,
                host,
                namespace,
                symbol,
                options,
                diagnostics,
            )?;
        }
        if let Some(symbol) = intrinsic {
            validate_jsx_namespace_type_symbol(store, symbol, location)?;
            if needs_intrinsics {
                intrinsic_elements = Some(resolve_namespace_export_type(
                    store,
                    host,
                    namespace,
                    symbol,
                    Some(&intrinsic_names),
                    options,
                    diagnostics,
                )?);
            }
        }
        if let Some(symbol) = element_type_symbol {
            element_type_constraint = resolve_jsx_element_type_constraint(
                store,
                host,
                namespace,
                symbol,
                options,
                diagnostics,
                location,
            )?;
        }
        if options.jsx_runtime != CanonicalJsxRuntime::Automatic
            && !plan.children.is_empty()
            && let Some(symbol) = children
        {
            validate_jsx_namespace_type_symbol(store, symbol, location)?;
            children_attribute = resolve_jsx_children_attribute(
                store,
                host,
                namespace,
                symbol,
                options,
                diagnostics,
                location,
            )?;
        }
    }

    Ok(JsxNamespace {
        element_type,
        element_type_constraint,
        intrinsic_elements,
        children_attribute,
        unknown_symbol,
        error_type,
        any_type,
    })
}

#[allow(clippy::too_many_arguments)] // Keep namespace ownership and diagnostic state explicit.
fn resolve_jsx_children_attribute(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    location: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let type_ =
        resolve_namespace_export_type(store, host, namespace, symbol, None, options, diagnostics)?;
    let properties = store
        .type_payload(type_)
        .and_then(|record| record.data().structured())
        .ok_or(SourceCheckError::Property(location))?
        .properties
        .as_deref()
        .unwrap_or_default();
    match properties {
        [] => Ok(None),
        [property] => {
            let record = store
                .symbol(*property)
                .ok_or(SourceCheckError::Property(location))?;
            if !record.flags().contains(SymbolFlags::PROPERTY)
                || record.name().as_utf8().is_none_or(str::is_empty)
            {
                return Err(SourceCheckError::Property(location));
            }
            Ok(Some(*property))
        }
        _ => {
            let declaration = store
                .symbol(symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first().copied())
                .ok_or(SourceCheckError::Property(location))?;
            add_diagnostic(diagnostics, declaration, 2608, ["ElementChildrenAttribute"])?;
            Ok(None)
        }
    }
}

fn validate_jsx_namespace_type_symbol(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    location: NodeRef,
) -> Result<(), SourceCheckError> {
    if store
        .symbol(symbol)
        .is_none_or(|record| !record.flags().intersects(SymbolFlags::TYPE))
    {
        return Err(SourceCheckError::Property(location));
    }
    Ok(())
}

fn resolve_jsx_namespace_element_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    if jsx_namespace_interface_has_heritage(store, host, namespace, symbol)? {
        resolve_inherited_jsx_element_identity(store, host, symbol)
    } else {
        resolve_namespace_export_type(store, host, namespace, symbol, None, options, diagnostics)
    }
}

/// Resolves a nongeneric `JSX.ElementType` alias and ignores unsupported enum declarations.
fn resolve_jsx_element_type_constraint(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    location: NodeRef,
) -> Result<Option<TypeId>, SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Property(location))?;
    if !record.flags().contains(SymbolFlags::TYPE_ALIAS) {
        return Ok(None);
    }
    let [declaration] = record
        .declarations()
        .ok_or(SourceCheckError::Property(location))?
    else {
        return Err(SourceCheckError::Property(location));
    };
    let declaration = *declaration;
    let node = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(declaration))?;
    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
        return Err(SourceCheckError::Property(declaration));
    };
    if record
        .flags()
        .without(SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT)
        != SymbolFlags::NONE
        || record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.get_parent_of_symbol(symbol) != Some(namespace)
        || node.kind != SyntaxKind::TypeAliasDeclaration
        || node.flags.0 != 0
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(SourceCheckError::Property(declaration));
    }
    if alias.type_parameters.is_some() {
        return Err(unsupported(declaration, SyntaxKind::TypeAliasDeclaration));
    }

    let resolved =
        resolve_namespace_export_type(store, host, namespace, symbol, None, options, diagnostics)?;
    if store
        .type_alias_links(symbol)
        .and_then(|links| links.type_parameters.as_deref())
        .is_some_and(|parameters| !parameters.is_empty())
    {
        return Err(unsupported(declaration, SyntaxKind::TypeAliasDeclaration));
    }
    let error_type = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?
        .error_type;
    Ok((resolved != error_type).then_some(resolved))
}

fn resolve_local_jsx_namespace(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    location: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let (arena, bound) = host.source(location).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingNode(location),
    ))?;
    let source = super::SourceFileRef::new(store.id(), bound.source_file());
    let Some(factory) = store
        .source_file_links(source)
        .map(|links| links.local_jsx_namespace.as_str())
        .filter(|namespace| !namespace.is_empty())
    else {
        return Ok(None);
    };

    let mut current = Some(location);
    let mut root = None;
    while let Some(node) = current {
        root = bound
            .locals(node)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(factory));
        if root.is_some() {
            break;
        }
        current = arena
            .get(node.node)
            .and_then(|record| record.parent)
            .map(|parent| child_ref(node, parent));
    }
    let root = root.or_else(|| {
        store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source(factory))
    });
    let Some(root) = root else {
        return Ok(None);
    };
    let root = resolve_local_jsx_namespace_alias(store, root, location)?;
    let owner = store
        .symbol(root)
        .ok_or(SourceCheckError::Property(location))?;
    if !owner.flags().intersects(SymbolFlags::MODULE) {
        return Ok(None);
    }
    let Some(exports) = store
        .module_symbol_links(root)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner.exports())
    else {
        return Ok(None);
    };
    let table = store
        .symbol_table(exports)
        .ok_or(SourceCheckError::Property(location))?;
    let Some(namespace) = table.get_source("JSX") else {
        return Ok(None);
    };
    let namespace = resolve_local_jsx_namespace_alias(store, namespace, location)?;
    let record = store
        .symbol(namespace)
        .ok_or(SourceCheckError::Property(location))?;
    if !record.flags().intersects(SymbolFlags::NAMESPACE)
        || record.name().as_utf8() != Some("JSX")
        || record.exports().is_none()
    {
        return Err(SourceCheckError::Property(location));
    }
    Ok(Some(namespace))
}

fn resolve_local_jsx_namespace_alias(
    store: &CanonicalTypeMapperStore,
    mut symbol: SemanticSymbolId,
    location: NodeRef,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let mut visited = HashSet::new();
    loop {
        symbol = store
            .get_merged_symbol(symbol)
            .ok_or(SourceCheckError::Import(location))?;
        let record = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Import(location))?;
        if !record.flags().contains(SymbolFlags::ALIAS) {
            return Ok(symbol);
        }
        if record.flags() != SymbolFlags::ALIAS || !visited.insert(symbol) {
            return Err(SourceCheckError::Import(location));
        }
        let links = store
            .alias_symbol_links(symbol)
            .ok_or(SourceCheckError::Import(location))?;
        if links.type_only_declaration.is_some() || links.immediate_target.is_none() {
            return Err(SourceCheckError::Import(location));
        }
        symbol = links
            .alias_target
            .symbol()
            .ok_or(SourceCheckError::Import(location))?;
    }
}

fn jsx_plan_intrinsic_names(plan: &JsxElementPlan) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_jsx_plan_intrinsic_names(plan, &mut names);
    names
}

fn collect_jsx_plan_intrinsic_names(plan: &JsxElementPlan, names: &mut HashSet<String>) {
    match &plan.kind {
        JsxElementPlanKind::Element {
            tag,
            attributes,
            closing,
            ..
        } => {
            if tag.intrinsic {
                names.insert(tag.name.clone());
            }
            if let Some(closing) = closing
                && closing.tag.intrinsic
            {
                names.insert(closing.tag.name.clone());
            }
            match attributes {
                JsxAttributesPlan::Properties(properties) => {
                    for property in properties {
                        if let JsxAttributeValue::Expression { value, .. } = &property.value {
                            collect_jsx_scalar_intrinsic_names(value, names);
                        }
                    }
                }
                JsxAttributesPlan::ObjectSpread(spread) => {
                    for property in &spread.properties {
                        if let JsxAttributeValue::Expression { value, .. } = &property.value {
                            collect_jsx_scalar_intrinsic_names(value, names);
                        }
                    }
                }
                JsxAttributesPlan::SourceSpread(spread) => {
                    collect_jsx_scalar_intrinsic_names(&spread.value, names);
                }
            }
        }
        JsxElementPlanKind::Fragment => {}
    }
    for child in &plan.children {
        match child {
            JsxChildPlan::Text { .. } => {}
            JsxChildPlan::Expression { value, .. } => {
                collect_jsx_scalar_intrinsic_names(value, names);
            }
            JsxChildPlan::Element(element) => collect_jsx_plan_intrinsic_names(element, names),
        }
    }
}

fn collect_jsx_scalar_intrinsic_names(scalar: &JsxScalarPlan, names: &mut HashSet<String>) {
    match scalar {
        JsxScalarPlan::Element(element) => collect_jsx_plan_intrinsic_names(element, names),
        JsxScalarPlan::Property { receiver, .. } => {
            collect_jsx_scalar_intrinsic_names(receiver, names);
        }
        JsxScalarPlan::TypeAssertion { value, .. } | JsxScalarPlan::Parenthesized { value, .. } => {
            collect_jsx_scalar_intrinsic_names(value, names);
        }
        JsxScalarPlan::Conditional {
            condition,
            when_true,
            when_false,
            ..
        } => {
            collect_jsx_scalar_intrinsic_names(condition, names);
            collect_jsx_scalar_intrinsic_names(when_true, names);
            collect_jsx_scalar_intrinsic_names(when_false, names);
        }
        JsxScalarPlan::AdjacentElements { left, right, .. } => {
            collect_jsx_plan_intrinsic_names(left, names);
            collect_jsx_plan_intrinsic_names(right, names);
        }
        JsxScalarPlan::String { .. }
        | JsxScalarPlan::Number { .. }
        | JsxScalarPlan::Boolean { .. }
        | JsxScalarPlan::Null(_)
        | JsxScalarPlan::GlobalThis(_)
        | JsxScalarPlan::Identifier { .. } => {}
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

fn resolve_inherited_jsx_element_identity(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<TypeId, SourceCheckError> {
    if store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .is_none()
    {
        let declaration = store
            .symbol(symbol)
            .and_then(|record| record.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .ok_or_else(|| invalid_namespace_symbol(symbol))?;
        let missing_links = usize::from(store.declared_type_links(symbol).is_none());
        let mut links = store
            .declared_type_links(symbol)
            .cloned()
            .unwrap_or_default();
        if !store.try_reserve_types(1) || !store.try_reserve_declared_type_links(missing_links) {
            return Err(SourceCheckError::Property(declaration));
        }
        let type_ = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .ok_or(SourceCheckError::Property(declaration))?;
        links.declared_type = Some(type_);
        if !store.set_declared_type_links(symbol, links) {
            return Err(SourceCheckError::Property(declaration));
        }
    }
    store
        .get_declared_type_of_symbol(host, symbol)
        .map_err(Into::into)
}

fn resolve_namespace_export_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    requested_intrinsic_names: Option<&HashSet<String>>,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or(invalid_namespace_symbol(symbol))?;
    if record.flags() == SymbolFlags::INTERFACE && record.parent() == Some(namespace) {
        return resolve_namespace_interface(
            store,
            host,
            namespace,
            symbol,
            requested_intrinsic_names,
            options,
            diagnostics,
        );
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
    requested_intrinsic_names: Option<&HashSet<String>>,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let (declaration, members, member_nodes, heritage) = {
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
            || interface.members.has_trailing_comma
            || !host.symbol_matches(store, *declaration, symbol)
        {
            return Err(unsupported(*declaration, node.kind));
        }
        (
            *declaration,
            record.members(),
            interface.members.nodes.clone(),
            interface.heritage_clauses.clone(),
        )
    };

    if let Some(heritage) = heritage {
        return resolve_record_intrinsic_namespace_interface(
            store,
            host,
            namespace,
            symbol,
            declaration,
            members,
            &member_nodes,
            &heritage,
            options,
            diagnostics,
        );
    }

    let mut property_symbols = Vec::new();
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
                let cached_type = match store.value_symbol_links(property_symbol) {
                    None => None,
                    Some(links) if links == &ValueSymbolLinks::default() => None,
                    Some(links) => {
                        let type_ = links
                            .resolved_type
                            .filter(|type_| store.type_payload(*type_).is_some())
                            .ok_or(SourceCheckError::Property(member))?;
                        let expected = ValueSymbolLinks {
                            resolved_type: Some(type_),
                            ..ValueSymbolLinks::default()
                        };
                        if links != &expected
                            || store
                                .type_node_links(annotation)
                                .and_then(|links| links.resolved_type)
                                .is_some_and(|resolved| resolved != type_)
                        {
                            return Err(SourceCheckError::Property(member));
                        }
                        Some(type_)
                    }
                };
                let type_ = if requested_intrinsic_names
                    .is_none_or(|requested| requested.contains(&name))
                    || jsx_intrinsic_property_has_call_signature(host, annotation)
                {
                    let cached_react = if let Some(cached) = cached_type
                        && store
                            .type_node_links(annotation)
                            .and_then(|links| links.resolved_type)
                            == Some(cached)
                        && store.validate_deferred_intersection_type(cached).is_ok()
                    {
                        deferred_react_class_attributes_base(store, host, cached, member)?
                            .map(|_| cached)
                    } else {
                        None
                    };
                    let resolved = if let Some(cached) = cached_react {
                        cached
                    } else {
                        CanonicalTypeQuery::new(store, host, options, diagnostics)?
                            .get_type_from_type_node(annotation)?
                    };
                    if cached_type.is_some_and(|cached| cached != resolved) {
                        return Err(SourceCheckError::Property(member));
                    }
                    Some(resolved)
                } else {
                    cached_type
                };
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
                property_symbols.push(property_symbol);
                if let Some(type_) = type_ {
                    properties.push(JsxNamespaceProperty {
                        symbol: property_symbol,
                        type_,
                    });
                }
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

    let existing_type = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type);
    if let Some(type_) = existing_type {
        let initialized = store
            .type_payload(type_)
            .ok_or(SourceCheckError::Property(declaration))?
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED);
        if initialized {
            validate_namespace_interface(
                store,
                type_,
                symbol,
                (members, &property_symbols),
                &properties,
                &indexes,
                declaration,
            )?;
            publish_namespace_property_links(store, &properties, declaration)?;
            return Ok(type_);
        }
        validate_unresolved_namespace_interface(store, type_, symbol, declaration)?;
    }

    if existing_type.is_none()
        && (!store.try_reserve_types(1) || !store.try_reserve_declared_type_links(1))
        || !store.try_reserve_index_infos(indexes.len())
    {
        return Err(SourceCheckError::Property(declaration));
    }
    reserve_namespace_property_links(store, &properties, declaration)?;

    let type_ = if let Some(type_) = existing_type {
        type_
    } else {
        let type_ = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .ok_or(SourceCheckError::Property(declaration))?;
        if !store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            },
        ) {
            return Err(SourceCheckError::Property(declaration));
        }
        type_
    };
    if !store.set_interface_base_resolution(type_, true, None, None) {
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
    publish_reserved_namespace_property_links(store, &properties, declaration)?;
    let property_symbols = (!property_symbols.is_empty()).then_some(property_symbols);
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

fn jsx_intrinsic_property_has_call_signature(host: &DeclaredTypeHost<'_>, node: NodeRef) -> bool {
    host.node(node).is_some_and(|record| {
        matches!(
            &record.data,
            NodeData::TypeLiteralNode(literal)
                if record.kind == SyntaxKind::TypeLiteral
                    && literal.members.nodes.iter().any(|member| {
                        host.node(child_ref(node, *member))
                            .is_some_and(|member| member.kind == SyntaxKind::CallSignature)
                    })
        )
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Keep inherited index publication atomic.
fn resolve_record_intrinsic_namespace_interface(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    members: Option<super::SymbolTableId>,
    member_nodes: &[ts_ast::NodeId],
    heritage: &ts_ast::NodeList,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let inherited = plan_record_intrinsic_heritage(
        store,
        host,
        namespace,
        symbol,
        declaration,
        members,
        member_nodes,
        heritage,
    )?;
    let mapped = CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_type_from_type_node(inherited.node)?;
    let (string_type, any_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        (bootstrap.string_type, bootstrap.any_type)
    };
    validate_record_intrinsic_base(
        store,
        inherited.alias,
        mapped,
        string_type,
        any_type,
        inherited.node,
    )?;
    store
        .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
        .map_err(|_| unsupported(inherited.node, SyntaxKind::ExpressionWithTypeArguments))?;
    let mapped_index = {
        let record = store
            .type_payload(mapped)
            .ok_or(SourceCheckError::Property(inherited.node))?;
        let super::TypeData::Mapped(mapped_record) = record.data() else {
            return Err(SourceCheckError::Property(inherited.node));
        };
        if !record
            .object_flags()
            .contains(ObjectFlags::INSTANTIATED_MAPPED | ObjectFlags::MEMBERS_RESOLVED)
            || mapped_record
                .object
                .structured
                .properties
                .as_ref()
                .is_some_and(|properties| !properties.is_empty())
        {
            return Err(SourceCheckError::Property(inherited.node));
        }
        let [index] = mapped_record
            .object
            .structured
            .index_infos
            .as_deref()
            .unwrap_or_default()
        else {
            return Err(SourceCheckError::Property(inherited.node));
        };
        let index_record = store
            .index_info(*index)
            .ok_or(SourceCheckError::Property(inherited.node))?;
        if index_record.key_type() != string_type
            || index_record.value_type() != any_type
            || index_record.is_readonly()
            || index_record.declaration().is_some()
            || index_record.index_symbol().is_some()
            || !index_record.components().is_empty()
        {
            return Err(SourceCheckError::Property(inherited.node));
        }
        *index
    };

    let type_ = store.get_declared_type_of_symbol(host, symbol)?;
    let state = {
        let record = store
            .type_payload(type_)
            .ok_or(SourceCheckError::Property(declaration))?;
        let super::TypeData::Interface(interface) = record.data() else {
            return Err(SourceCheckError::Property(declaration));
        };
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || interface.resolved_base_constructor_type.is_some()
        {
            return Err(SourceCheckError::Property(declaration));
        }
        if interface.base_types_resolved {
            Some((
                interface.resolved_base_types.clone(),
                interface.declared_members_resolved,
                interface.declared_members,
                interface.declared_index_infos.clone(),
                interface.reference.object.structured.clone(),
                record.object_flags(),
            ))
        } else {
            if interface.resolved_base_types.is_some()
                || interface.declared_members_resolved
                || interface.declared_members.is_some()
                || interface.declared_index_infos.is_some()
                || interface.reference.object.structured
                    != super::type_records::StructuredTypeData::default()
            {
                return Err(SourceCheckError::Property(declaration));
            }
            None
        }
    };
    if let Some((bases, declared, declared_members, declared_indexes, structured, flags)) = state {
        let [base] = bases.as_deref().unwrap_or_default() else {
            return Err(SourceCheckError::Property(declaration));
        };
        let [index] = structured.index_infos.as_deref().unwrap_or_default() else {
            return Err(SourceCheckError::Property(declaration));
        };
        let index_record = store
            .index_info(*index)
            .ok_or(SourceCheckError::Property(declaration))?;
        if *base != mapped
            || !declared
            || declared_members != members
            || declared_indexes.is_some()
            || structured.members != members
            || structured.properties.is_some()
            || structured.signatures.is_some()
            || structured.call_signature_count != 0
            || !flags.contains(ObjectFlags::MEMBERS_RESOLVED)
            || *index == mapped_index
            || index_record.key_type() != string_type
            || index_record.value_type() != any_type
            || index_record.is_readonly()
            || index_record.declaration().is_some()
            || !index_record.components().is_empty()
        {
            return Err(SourceCheckError::Property(declaration));
        }
        if let Some(index_symbol) = index_record.index_symbol() {
            validate_index_symbol(
                store,
                index_symbol,
                Some(symbol),
                None,
                any_type,
                declaration,
            )?;
        }
        return Ok(type_);
    }

    if !store.try_reserve_index_infos(1) {
        return Err(SourceCheckError::Property(declaration));
    }
    let index = store
        .alloc_index_info(string_type, any_type, false, None, Vec::new())
        .ok_or(SourceCheckError::Property(declaration))?;
    if !store.set_interface_base_resolution(type_, true, None, Some(vec![mapped]))
        || !store.set_interface_declared_members(type_, true, members, None, None, None)
        || !store.set_structured_type_members(type_, members, None, None, None, Some(vec![index]))
    {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(type_)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Heritage syntax requires one complete proof.
fn plan_record_intrinsic_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    members: Option<super::SymbolTableId>,
    member_nodes: &[ts_ast::NodeId],
    heritage: &ts_ast::NodeList,
) -> Result<JsxRecordHeritage, SourceCheckError> {
    let unsupported_interface = || unsupported(declaration, SyntaxKind::InterfaceDeclaration);
    if store
        .symbol(namespace)
        .and_then(|record| record.name().as_utf8())
        != Some("JSX")
        || store
            .symbol(symbol)
            .and_then(|record| record.name().as_utf8())
            != Some("IntrinsicElements")
        || !member_nodes.is_empty()
        || members
            .and_then(|members| store.symbol_table(members))
            .is_some_and(|members| !members.is_empty())
        || heritage.has_trailing_comma
        || heritage.nodes.len() != 1
    {
        return Err(unsupported_interface());
    }
    let clause = child_ref(declaration, heritage.nodes[0]);
    let clause_record = host
        .node(clause)
        .ok_or(SourceCheckError::Property(clause))?;
    let NodeData::HeritageClause(clause_data) = &clause_record.data else {
        return Err(unsupported(clause, clause_record.kind));
    };
    if clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || clause_data.token != SyntaxKind::ExtendsKeyword
        || clause_data.facts != 0
        || clause_data.types.has_trailing_comma
        || clause_data.types.nodes.len() != 1
    {
        return Err(unsupported(clause, clause_record.kind));
    }
    let node = child_ref(clause, clause_data.types.nodes[0]);
    let record = host.node(node).ok_or(SourceCheckError::Property(node))?;
    let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
        return Err(unsupported(node, record.kind));
    };
    let Some(arguments) = expression.type_arguments.as_ref() else {
        return Err(unsupported(node, record.kind));
    };
    if record.kind != SyntaxKind::ExpressionWithTypeArguments
        || record.parent != Some(clause.node)
        || record.flags.0 != 0
        || expression.facts != 0
        || arguments.has_trailing_comma
        || arguments.nodes.len() != 2
    {
        return Err(unsupported(node, record.kind));
    }
    let name = child_ref(node, expression.expression);
    let name_record = host.node(name).ok_or(SourceCheckError::Property(name))?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(name, name_record.kind));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(node.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text != "Record"
    {
        return Err(unsupported(name, name_record.kind));
    }
    for (argument, expected) in arguments
        .nodes
        .iter()
        .zip([SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword])
    {
        let argument = child_ref(node, *argument);
        let argument_record = host
            .node(argument)
            .ok_or(SourceCheckError::Property(argument))?;
        if argument_record.kind != expected
            || !matches!(&argument_record.data, NodeData::KeywordTypeNode(_))
            || argument_record.parent != Some(node.node)
            || argument_record.flags.0 != 0
        {
            return Err(unsupported(argument, argument_record.kind));
        }
    }
    let alias = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(super::DeclaredTypeError::from)?
        .and_then(|alias| store.get_merged_symbol(alias))
        .ok_or_else(unsupported_interface)?;
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Record"))
        .and_then(|global| store.get_merged_symbol(global));
    if Some(alias) != global
        || store
            .symbol(alias)
            .is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
    {
        return Err(unsupported_interface());
    }
    Ok(JsxRecordHeritage { node, alias })
}

fn validate_record_intrinsic_base(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    mapped: TypeId,
    string_type: TypeId,
    any_type: TypeId,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .type_payload(mapped)
        .ok_or(SourceCheckError::Property(node))?;
    let identity = record
        .alias()
        .and_then(|identity| store.type_alias(identity))
        .ok_or(SourceCheckError::Property(node))?;
    if identity.symbol() != Some(alias)
        || identity.type_arguments() != Some([string_type, any_type].as_slice())
    {
        return Err(SourceCheckError::Property(node));
    }
    let links = store
        .type_alias_links(alias)
        .ok_or(SourceCheckError::Property(node))?;
    let declared = links
        .declared_type
        .ok_or(SourceCheckError::Property(node))?;
    let parameters = links
        .type_parameters
        .as_deref()
        .ok_or(SourceCheckError::Property(node))?;
    store
        .validate_record_mapped_alias_instantiation(
            alias,
            declared,
            parameters,
            &[string_type, any_type],
            mapped,
        )
        .map_err(|_| SourceCheckError::Property(node))
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

fn reserve_namespace_property_links(
    store: &mut CanonicalTypeMapperStore,
    properties: &[JsxNamespaceProperty],
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    let mut missing = 0;
    for property in properties {
        let expected = ValueSymbolLinks {
            resolved_type: Some(property.type_),
            ..ValueSymbolLinks::default()
        };
        match store.value_symbol_links(property.symbol) {
            Some(links) if links == &expected => {}
            None => missing += 1,
            Some(links) if links == &ValueSymbolLinks::default() => missing += 1,
            Some(_) => return Err(SourceCheckError::Property(declaration)),
        }
    }
    if missing != 0 && !store.try_reserve_value_symbol_links(missing) {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(())
}

fn publish_reserved_namespace_property_links(
    store: &mut CanonicalTypeMapperStore,
    properties: &[JsxNamespaceProperty],
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    for property in properties {
        let expected = ValueSymbolLinks {
            resolved_type: Some(property.type_),
            ..ValueSymbolLinks::default()
        };
        if store.value_symbol_links(property.symbol) != Some(&expected)
            && !store.set_value_symbol_links(property.symbol, expected)
        {
            return Err(SourceCheckError::Property(declaration));
        }
    }
    Ok(())
}

fn publish_namespace_property_links(
    store: &mut CanonicalTypeMapperStore,
    properties: &[JsxNamespaceProperty],
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    reserve_namespace_property_links(store, properties, declaration)?;
    publish_reserved_namespace_property_links(store, properties, declaration)
}

fn validate_unresolved_namespace_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceCheckError::Property(declaration))?;
    let super::TypeData::Interface(interface) = record.data() else {
        return Err(SourceCheckError::Property(declaration));
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::INTERFACE
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
        || interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || interface.declared_members_resolved
        || interface.declared_members.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || interface.reference.object.structured
            != super::type_records::StructuredTypeData::default()
    {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(())
}

fn validate_namespace_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    symbol: SemanticSymbolId,
    members: (Option<super::SymbolTableId>, &[SemanticSymbolId]),
    properties: &[JsxNamespaceProperty],
    indexes: &[JsxNamespaceIndex],
    declaration: NodeRef,
) -> Result<(), SourceCheckError> {
    let (members, property_symbols) = members;
    let record = store
        .type_payload(type_)
        .ok_or(SourceCheckError::Property(declaration))?;
    let super::TypeData::Interface(interface) = record.data() else {
        return Err(SourceCheckError::Property(declaration));
    };
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
            != property_symbols
        || existing_indexes.len() != indexes.len()
    {
        return Err(SourceCheckError::Property(declaration));
    }
    for property in properties {
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
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    plan: &JsxElementPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let (arena, bound, host, _) = source;
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
            if options.jsx_runtime == CanonicalJsxRuntime::Classic && !plan.children.is_empty() {
                children_checked = check_react_jsx_fragment_children(
                    store,
                    source,
                    namespace,
                    plan,
                    options,
                    diagnostics,
                )?;
            }
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
                        (arena, bound, host),
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
                    source,
                    namespace,
                    plan.opening,
                    tag,
                    attributes,
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
                        (arena, bound, host),
                        namespace,
                        closing,
                        options,
                        diagnostics,
                    )?;
                }
                (attributes_type, signature)
            };

            publish_signature_links(store, plan.opening, signature)?;
            check_jsx_element_type_constraint(store, host, namespace, tag, diagnostics)?;
            let children = if options.jsx_runtime == CanonicalJsxRuntime::Automatic
                || namespace.children_attribute.is_some()
            {
                check_jsx_implicit_children(
                    store,
                    source,
                    namespace,
                    plan,
                    attributes,
                    expected_attributes,
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
                        source,
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
                        source,
                        namespace,
                        expected_attributes,
                        spread,
                        options,
                        diagnostics,
                    )?;
                    publish_type_links(store, *attributes_node, actual)?;
                    (checked, actual)
                }
                JsxAttributesPlan::SourceSpread(spread) => {
                    let checked = check_jsx_source_spread(
                        store,
                        source,
                        namespace,
                        spread,
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
            };
            check_attribute_assignability(
                store,
                host,
                plan.opening,
                tag,
                (expected_attributes, actual_attributes),
                &checked,
                children,
                options,
                diagnostics,
            )?;
        }
    }

    if !children_checked {
        for child in &plan.children {
            match child {
                JsxChildPlan::Text { .. } => {}
                JsxChildPlan::Expression { wrapper, value } => {
                    let type_ =
                        execute_scalar(store, source, namespace, value, options, diagnostics)?;
                    publish_type_links(store, *wrapper, type_)?;
                }
                JsxChildPlan::Element(element) => {
                    execute_jsx_element(store, source, namespace, element, options, diagnostics)?;
                }
            }
        }
    }

    publish_type_links(store, plan.expression, namespace.element_type)?;
    Ok(namespace.element_type)
}

fn check_jsx_element_type_constraint(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: &JsxNamespace,
    tag: &JsxTagPlan,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let Some(constraint) = namespace.element_type_constraint else {
        return Ok(());
    };
    let tag_type = if tag.intrinsic {
        store.regular_string_literal_type(tag.name.clone())?
    } else {
        store
            .type_node_links(tag.node)
            .and_then(|links| links.resolved_type)
            .filter(|type_| store.type_payload(*type_).is_some())
            .ok_or(SourceCheckError::Property(tag.node))?
    };
    if store.is_type_assignable_to(tag_type, constraint)? {
        return Ok(());
    }

    let formatted = type_to_string_with_host_and_flags(
        store,
        host,
        tag_type,
        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
    )?;
    let detail = Diagnostic::with_arguments(
        message_by_code(18_053).ok_or(SourceCheckError::MissingDiagnostic(18_053))?,
        [formatted],
    )
    .render()
    .map_err(|_| SourceCheckError::MissingDiagnostic(18_053))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(tag.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2786).ok_or(SourceCheckError::MissingDiagnostic(2786))?,
                [tag.name.clone()],
            )
            .with_details([format!("  {detail}")]),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn check_react_jsx_fragment_children(
    store: &mut CanonicalTypeMapperStore,
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    plan: &JsxElementPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<bool, SourceCheckError> {
    let (arena, bound, host, _) = source;
    let source_file = super::SourceFileRef::new(store.id(), bound.source_file());
    let factory = store
        .source_file_links(source_file)
        .map(|links| links.local_jsx_fragment_namespace.as_str())
        .filter(|factory| !factory.is_empty())
        .unwrap_or("React");
    let Some(owner) =
        resolve_scoped_jsx_namespace_symbol(store, arena, bound, plan.opening, factory)?
    else {
        return Ok(false);
    };
    let Some(owner_record) = store.symbol(owner) else {
        return Err(SourceCheckError::Property(plan.opening));
    };
    if !owner_record.flags().intersects(SymbolFlags::MODULE) {
        return Ok(false);
    }
    let Some(fragment) = owner_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("Fragment"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let record = store
        .symbol(fragment)
        .ok_or(SourceCheckError::Property(plan.opening))?;
    if !record.flags().intersects(SymbolFlags::VALUE)
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_utf8() != Some("Fragment")
        || store.get_parent_of_symbol(fragment) != Some(owner)
        || record.value_declaration().is_none()
    {
        return Err(SourceCheckError::Property(plan.opening));
    }
    let member = JsxNamespaceMemberPlan {
        namespace: owner,
        namespace_node: plan.opening,
        member: fragment,
        member_node: plan.opening,
    };
    let component =
        resolve_namespace_component_type(store, host, &member, plan.opening, options, diagnostics)?;
    let attributes = match validate_stored_callable_set(store, component) {
        StoredCallableSetValidation::Valid { projection, .. }
            if projection.construct_signatures.is_empty()
                && projection.call_signatures.len() == 1 =>
        {
            let callable = &projection.call_signatures[0];
            let [attributes] = callable.parameters.as_slice() else {
                return Err(SourceCheckError::Call(plan.opening));
            };
            *attributes
        }
        StoredCallableSetValidation::NotCallable => {
            authenticated_fragment_component_attributes(store, host, fragment, plan.opening)?
        }
        StoredCallableSetValidation::Pending { .. }
        | StoredCallableSetValidation::Malformed { .. }
        | StoredCallableSetValidation::Valid { .. } => {
            return Err(SourceCheckError::Call(plan.opening));
        }
    };
    let signature = intrinsic_signature(store, plan.opening, attributes, namespace.element_type)?;
    publish_signature_links(store, plan.opening, signature)?;
    let empty = JsxAttributesPlan::Properties(Vec::new());
    let Some(children) = check_jsx_implicit_children(
        store,
        source,
        namespace,
        plan,
        &empty,
        attributes,
        options,
        diagnostics,
    )?
    else {
        return Ok(false);
    };
    let property_name = checked_jsx_children_name(store, children)?.to_owned();
    let Some(expected) = resolve_expected_jsx_child_type(
        store,
        host,
        attributes,
        &property_name,
        plan.opening,
        options,
        diagnostics,
    )?
    else {
        return Ok(true);
    };
    if children.individual_errors || store.is_type_assignable_to(children.type_, expected)? {
        return Ok(true);
    }

    let actual = format_attribute_object(store, host, &[], Some(children))?;
    let expected_object = type_to_string_with_host_and_flags(
        store,
        host,
        attributes,
        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
    )?;
    let display = get_type_names_for_assignability_error(store, children.type_, expected)?;
    let property_detail = Diagnostic::with_arguments(
        message_by_code(2326).ok_or(SourceCheckError::MissingDiagnostic(2326))?,
        [property_name],
    )
    .render()
    .map_err(|_| SourceCheckError::MissingDiagnostic(2326))?;
    let value_detail = Diagnostic::with_arguments(
        message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
        [display.source, display.target],
    )
    .render()
    .map_err(|_| SourceCheckError::MissingDiagnostic(2322))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(plan.opening),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                [actual, expected_object],
            )
            .with_details([
                format!("  {property_detail}"),
                format!("    {value_detail}"),
            ]),
            related_information: Vec::new(),
        },
    );
    Ok(true)
}

fn resolve_expected_jsx_child_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expected: TypeId,
    name: &str,
    location: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Option<TypeId>, SourceCheckError> {
    let record = store
        .type_payload(expected)
        .ok_or(SourceCheckError::Property(location))?;
    if record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN) {
        return Ok(None);
    }
    if let Some(property) = record
        .data()
        .structured()
        .and_then(|structured| structured.members)
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(name))
        && let Some(type_) = store
            .value_symbol_links(property)
            .and_then(|links| links.resolved_type)
    {
        return Ok(Some(type_));
    }

    if name != "children" {
        return Ok(None);
    }
    let Some(attributes) = deferred_react_class_attributes_base(store, host, expected, location)?
    else {
        return Ok(None);
    };
    let namespace = store
        .get_parent_of_symbol(attributes)
        .ok_or(SourceCheckError::Property(location))?;
    let react_node = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("ReactNode"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Property(location))?;
    let alias = store
        .symbol(react_node)
        .ok_or(SourceCheckError::Property(location))?;
    if !alias.flags().contains(SymbolFlags::TYPE_ALIAS)
        || store.get_parent_of_symbol(react_node) != Some(namespace)
    {
        return Err(SourceCheckError::Property(location));
    }
    CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_declared_type_of_symbol(react_node)
        .map(Some)
        .map_err(Into::into)
}

#[allow(clippy::too_many_arguments)] // Contextual children retain their owner and expected props.
fn check_jsx_implicit_children(
    store: &mut CanonicalTypeMapperStore,
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    plan: &JsxElementPlan,
    attributes: &JsxAttributesPlan,
    expected_attributes: TypeId,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Option<CheckedJsxChildren>, SourceCheckError> {
    if plan.children.is_empty() {
        return Ok(None);
    }
    let name = if options.jsx_runtime == CanonicalJsxRuntime::Automatic {
        None
    } else {
        namespace.children_attribute
    };
    let property_name = name.map_or_else(
        || Ok("children".to_owned()),
        |symbol| {
            store
                .symbol(symbol)
                .and_then(|record| record.name().as_utf8())
                .map(str::to_owned)
                .ok_or(SourceCheckError::Property(plan.opening))
        },
    )?;
    match attributes {
        JsxAttributesPlan::Properties(attributes)
            if attributes
                .iter()
                .any(|attribute| attribute.name == property_name) =>
        {
            return Err(unsupported(plan.opening, SyntaxKind::JsxAttributes));
        }
        JsxAttributesPlan::ObjectSpread(spread) => {
            if options.jsx_runtime == CanonicalJsxRuntime::Automatic {
                return Err(unsupported(spread.node, SyntaxKind::JsxSpreadAttribute));
            }
            return Ok(None);
        }
        JsxAttributesPlan::Properties(_) | JsxAttributesPlan::SourceSpread(_) => {}
    }

    let mut first_node = None;
    let mut child_types = Vec::with_capacity(plan.children.len());
    let expected_child = if plan.children.len() > 1 {
        resolve_expected_jsx_child_type(
            store,
            source.2,
            expected_attributes,
            &property_name,
            plan.opening,
            options,
            diagnostics,
        )?
    } else {
        None
    };
    let mut individual_errors = false;
    for child in &plan.children {
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
                let type_ = execute_scalar(store, source, namespace, value, options, diagnostics)?;
                publish_type_links(store, *wrapper, type_)?;
                (*wrapper, type_)
            }
            JsxChildPlan::Element(element) => {
                let type_ =
                    execute_jsx_element(store, source, namespace, element, options, diagnostics)?;
                (element.expression, type_)
            }
        };
        first_node.get_or_insert(node);
        if let Some(expected) = expected_child
            && !store.is_type_assignable_to(type_, expected)?
        {
            let display = get_type_names_for_assignability_error(store, type_, expected)?;
            add_diagnostic(diagnostics, node, 2322, [display.source, display.target])?;
            individual_errors = true;
        }
        child_types.push(type_);
    }

    let node = first_node.expect("a nonempty JSX child plan has a first child");
    let type_ = if let [type_] = child_types.as_slice() {
        *type_
    } else {
        let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
        let element = store.literal_union_type_prepared(&child_types, None, &mut prepared)?;
        automatic_jsx_children_array_type(store, source.2, element, node)?
    };
    Ok(Some(CheckedJsxChildren {
        node,
        type_,
        name,
        individual_errors,
    }))
}

fn automatic_jsx_children_array_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    element: TypeId,
    location: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let (globals, fallback) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        (bootstrap.globals, bootstrap.empty_generic_type)
    };
    let array = store
        .symbol_table(globals)
        .ok_or(SourceCheckError::Property(location))?
        .get_source("Array");
    let target = if let Some(array) = array {
        let array = store
            .get_merged_symbol(array)
            .ok_or(SourceCheckError::Property(location))?;
        let record = store
            .symbol(array)
            .ok_or(SourceCheckError::Property(location))?;
        if record
            .flags()
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        {
            let declared = store.get_declared_type_of_symbol(host, array)?;
            let record = store
                .type_payload(declared)
                .ok_or(SourceCheckError::Property(location))?;
            let super::TypeData::Interface(interface) = record.data() else {
                return Err(SourceCheckError::Property(location));
            };
            if interface
                .all_type_parameters
                .as_ref()
                .is_some_and(|parameters| parameters.len() == 2)
            {
                declared
            } else {
                fallback
            }
        } else {
            fallback
        }
    } else {
        fallback
    };

    super::global_types::create_type_from_generic_global_type(
        store,
        target,
        element,
        ObjectFlags::NONE,
    )
    .map_err(super::array_types::ArrayTypeError::from)
    .map_err(SourceCheckError::from)
}

fn check_jsx_closing_tag(
    store: &mut CanonicalTypeMapperStore,
    source: (&NodeArena, &BoundFile, &DeclaredTypeHost<'_>),
    namespace: &JsxNamespace,
    closing: &JsxClosingPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let (arena, bound, host) = source;
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

    if let Some(member) = &closing.tag.namespace_member {
        let component = resolve_namespace_component_type(
            store,
            host,
            member,
            closing.tag.node,
            options,
            diagnostics,
        )?;
        publish_namespace_component_tag_links(store, member, &closing.tag, component)?;
        return Ok(());
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
            let declarations = if let Some(declaration) = declaration {
                if !bound.contains(declaration)
                    && !authenticated_foreign_intrinsic_index_declaration(store, owner, declaration)
                {
                    return Err(SourceCheckError::Property(opening));
                }
                Some(vec![declaration])
            } else {
                validate_inherited_record_intrinsic_index(
                    store,
                    intrinsic_elements,
                    index,
                    owner,
                    opening,
                )?;
                None
            };
            if !store.try_reserve_checker_symbol_allocations(1, 0)
                || !store.try_reserve_value_symbol_links(1)
            {
                return Err(SourceCheckError::Property(opening));
            }
            let symbol = store
                .alloc_symbol(SymbolData {
                    flags: SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                    check_flags: CheckFlags::INDEX_SYMBOL,
                    name: EscapedName::internal(InternalSymbolName::Index),
                    declarations,
                    value_declaration: declaration,
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

fn authenticated_foreign_intrinsic_index_declaration(
    store: &CanonicalTypeMapperStore,
    owner: Option<SemanticSymbolId>,
    declaration: NodeRef,
) -> bool {
    let Some(owner) = owner else {
        return false;
    };
    let Some(super::store::SourceNodeParent::Parent(interface)) =
        store.source_node_parent(declaration)
    else {
        return false;
    };
    store.source_node_kind(declaration) == Some(SyntaxKind::IndexSignature)
        && store.source_node_kind(interface) == Some(SyntaxKind::InterfaceDeclaration)
        && store.symbol(owner).is_some_and(|record| {
            record.flags() == SymbolFlags::INTERFACE
                && record
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&interface))
        })
}

fn validate_inherited_record_intrinsic_index(
    store: &CanonicalTypeMapperStore,
    intrinsics: TypeId,
    index: super::IndexInfoId,
    owner: Option<SemanticSymbolId>,
    location: NodeRef,
) -> Result<(), SourceCheckError> {
    let invalid = || unsupported(location, SyntaxKind::IndexSignature);
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let string_type = bootstrap.string_type;
    let any_type = bootstrap.any_type;
    let alias = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Record"))
        .and_then(|alias| store.get_merged_symbol(alias))
        .ok_or_else(invalid)?;
    let record = store.type_payload(intrinsics).ok_or_else(invalid)?;
    let super::TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    let [base] = interface.resolved_base_types.as_deref().unwrap_or_default() else {
        return Err(invalid());
    };
    let [derived_index] = interface
        .reference
        .object
        .structured
        .index_infos
        .as_deref()
        .unwrap_or_default()
    else {
        return Err(invalid());
    };
    let mapped_index = store
        .type_payload(*base)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.index_infos.as_deref())
        .and_then(|indexes| match indexes {
            [index] => Some(*index),
            _ => None,
        })
        .ok_or_else(invalid)?;
    let derived = store.index_info(*derived_index).ok_or_else(invalid)?;
    let original = store.index_info(mapped_index).ok_or_else(invalid)?;
    if record.symbol() != owner
        || !interface.base_types_resolved
        || *derived_index != index
        || *derived_index == mapped_index
        || derived.key_type() != string_type
        || derived.value_type() != any_type
        || derived.is_readonly()
        || derived.declaration().is_some()
        || !derived.components().is_empty()
        || original.key_type() != string_type
        || original.value_type() != any_type
        || original.is_readonly()
        || original.declaration().is_some()
        || original.index_symbol().is_some()
        || !original.components().is_empty()
    {
        return Err(invalid());
    }
    validate_record_intrinsic_base(store, alias, *base, string_type, any_type, location)
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

#[allow(clippy::too_many_arguments)] // Generic JSX needs its authenticated attribute source.
fn resolve_component_tag(
    store: &mut CanonicalTypeMapperStore,
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    opening: NodeRef,
    tag: &JsxTagPlan,
    attributes: &JsxAttributesPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(TypeId, SignatureId), SourceCheckError> {
    let (arena, bound, host, global_types) = source;
    let (symbol, component) = if let Some(member) = &tag.namespace_member {
        let component =
            resolve_namespace_component_type(store, host, member, tag.node, options, diagnostics)?;
        publish_namespace_component_tag_links(store, member, tag, component)?;
        (member.member, component)
    } else {
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
        (symbol, component)
    };
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
        StoredCallableSetValidation::NotCallable
            if tag.namespace_member.is_some()
                && store
                    .symbol(symbol)
                    .and_then(|record| record.name().as_utf8())
                    == Some("Fragment") =>
        {
            let attributes =
                authenticated_fragment_component_attributes(store, host, symbol, tag.node)?;
            let signature =
                intrinsic_signature(store, opening, attributes, namespace.element_type)?;
            return Ok((attributes, signature));
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
    if signature.this_parameter().is_some()
        || signature.has_rest_parameter()
        || callable.min_argument_count > 1
        || callable.parameters.len() > 1
    {
        return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
    }
    if !signature.type_parameters().is_empty() {
        let Some(global_types) = global_types else {
            return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
        };
        let JsxAttributesPlan::SourceSpread(spread) = attributes else {
            return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
        };
        let argument = execute_scalar(
            store,
            source,
            namespace,
            &spread.value,
            options,
            diagnostics,
        )?;
        let signature = resolve_jsx_generic_component_signature(
            store,
            host,
            global_types,
            options,
            diagnostics,
            opening,
            component,
            argument,
        )?;
        let [parameter] = store
            .signature(signature)
            .ok_or(SourceCheckError::Call(opening))?
            .parameters()
        else {
            return Err(SourceCheckError::Call(opening));
        };
        let attributes_type = store
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type)
            .ok_or(SourceCheckError::Call(opening))?;
        resolve_jsx_spread_members(store, attributes_type, Some(global_types), opening)?;
        return Ok((attributes_type, signature));
    }
    if callable.return_type.is_none() {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
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

fn resolve_namespace_component_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: &JsxNamespaceMemberPlan,
    location: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    if let Some(links) = store.value_symbol_links(member.member)
        && links != &ValueSymbolLinks::default()
    {
        let type_ = links
            .resolved_type
            .filter(|type_| store.type_payload(*type_).is_some())
            .ok_or(SourceCheckError::Property(location))?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(SourceCheckError::Property(location));
        }
        return Ok(type_);
    }

    let record = store
        .symbol(member.member)
        .ok_or(SourceCheckError::Property(location))?;
    let declaration = record
        .value_declaration()
        .ok_or(SourceCheckError::Property(location))?;
    let declaration_record = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(declaration))?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(SourceCheckError::Property(declaration));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || !host.symbol_matches(store, declaration, member.member)
        || store.get_parent_of_symbol(member.member) != Some(member.namespace)
    {
        return Err(SourceCheckError::Property(declaration));
    }
    let annotation = variable
        .type_
        .map(|annotation| child_ref(declaration, annotation))
        .ok_or(SourceCheckError::Property(declaration))?;
    let annotation_record = host
        .node(annotation)
        .ok_or(SourceCheckError::Property(annotation))?;
    if annotation_record.parent != Some(declaration.node) || annotation_record.flags.0 != 0 {
        return Err(SourceCheckError::Property(annotation));
    }

    let type_ = if let NodeData::TypeReferenceNode(reference) = &annotation_record.data
        && record.name().as_utf8() == Some("Fragment")
    {
        let name = child_ref(annotation, reference.type_name);
        let name_record = host.node(name).ok_or(SourceCheckError::Property(name))?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(SourceCheckError::Property(name));
        };
        let arguments = reference
            .type_arguments
            .as_ref()
            .ok_or(SourceCheckError::Property(annotation))?;
        let [attributes] = arguments.nodes.as_slice() else {
            return Err(SourceCheckError::Property(annotation));
        };
        let attributes = child_ref(annotation, *attributes);
        let attributes_record = host
            .node(attributes)
            .ok_or(SourceCheckError::Property(attributes))?;
        let component = store
            .symbol(member.namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("ExoticComponent"))
            .and_then(|component| store.get_merged_symbol(component))
            .ok_or(SourceCheckError::Property(annotation))?;
        let component_record = store
            .symbol(component)
            .ok_or(SourceCheckError::Property(annotation))?;
        let call = component_record
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::Call.as_ref()))
            .and_then(|call| store.get_merged_symbol(call))
            .ok_or(SourceCheckError::Property(annotation))?;
        let call_record = store
            .symbol(call)
            .ok_or(SourceCheckError::Property(annotation))?;
        if annotation_record.kind != SyntaxKind::TypeReference
            || arguments.has_trailing_comma
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(annotation.node)
            || identifier.flow_node.is_some()
            || identifier.text != "ExoticComponent"
            || attributes_record.parent != Some(annotation.node)
            || !component_record.flags().contains(SymbolFlags::INTERFACE)
            || component_record
                .flags()
                .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
                != SymbolFlags::NONE
            || component_record.check_flags() != CheckFlags::NONE
            || store.get_parent_of_symbol(component) != Some(member.namespace)
            || call_record.flags() != SymbolFlags::SIGNATURE
            || call_record.check_flags() != CheckFlags::NONE
            || store.get_parent_of_symbol(call) != Some(component)
        {
            return Err(SourceCheckError::Property(annotation));
        }
        let attributes = CanonicalTypeQuery::new(store, host, options, diagnostics)?
            .get_type_from_type_node(attributes)?;
        let target = store.get_declared_type_of_symbol(host, component)?;
        create_direct_generic_reference(store, target, &[attributes], ObjectFlags::FROM_TYPE_NODE)
            .map_err(|_| SourceCheckError::Property(annotation))?
    } else {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
            .get_type_from_type_node(annotation)?
    };
    publish_type_links(store, annotation, type_)?;
    publish_attribute_value_links(store, member.member, type_, declaration)?;
    Ok(type_)
}

fn authenticated_fragment_component_attributes(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    location: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let component = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Property(location))?;
    let reference = validate_direct_generic_reference(store, component)
        .map_err(|_| SourceCheckError::Property(location))?;
    let [attributes] = reference.type_arguments.as_slice() else {
        return Err(SourceCheckError::Property(location));
    };
    let target = store
        .type_payload(reference.target)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(SourceCheckError::Property(location))?;
    if store
        .symbol(target)
        .and_then(|record| record.name().as_utf8())
        != Some("ExoticComponent")
        || store
            .symbol(symbol)
            .and_then(|record| record.name().as_utf8())
            != Some("Fragment")
        || host
            .node(
                store
                    .symbol(symbol)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    .ok_or(SourceCheckError::Property(location))?,
            )
            .is_none()
    {
        return Err(SourceCheckError::Property(location));
    }
    Ok(*attributes)
}

fn publish_namespace_component_tag_links(
    store: &mut CanonicalTypeMapperStore,
    member: &JsxNamespaceMemberPlan,
    tag: &JsxTagPlan,
    component: TypeId,
) -> Result<(), SourceCheckError> {
    let namespace = jsx_namespace_value_type(store, member.namespace, member.namespace_node)?;
    publish_symbol_links(store, member.namespace_node, member.namespace)?;
    publish_type_links(store, member.namespace_node, namespace)?;
    publish_symbol_links(store, member.member_node, member.member)?;
    publish_type_links(store, member.member_node, component)?;
    publish_symbol_links(store, tag.node, member.member)?;
    publish_type_links(store, tag.node, component)
}

fn jsx_namespace_value_type(
    store: &mut CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    location: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let owner = store
        .symbol(namespace)
        .ok_or(SourceCheckError::Property(location))?;
    let exports = owner
        .exports()
        .ok_or(SourceCheckError::Property(location))?;
    let properties = store
        .symbol_table(exports)
        .ok_or(SourceCheckError::Property(location))?
        .iter()
        .filter_map(|(_, symbol)| {
            store
                .symbol(symbol)
                .filter(|record| record.flags().intersects(SymbolFlags::VALUE))
                .map(|_| symbol)
        })
        .collect::<Vec<_>>();
    if let Some(links) = store.value_symbol_links(namespace)
        && links != &ValueSymbolLinks::default()
    {
        let type_ = links
            .resolved_type
            .ok_or(SourceCheckError::Property(location))?;
        let record = store
            .type_payload(type_)
            .ok_or(SourceCheckError::Property(location))?;
        let structured = record
            .data()
            .structured()
            .ok_or(SourceCheckError::Property(location))?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
            || record.symbol() != Some(namespace)
            || structured.members != Some(exports)
            || structured.properties.as_deref() != Some(properties.as_slice())
        {
            return Err(SourceCheckError::Property(location));
        }
        return Ok(type_);
    }
    if !store.try_reserve_types(1) || !store.try_reserve_value_symbol_links(1) {
        return Err(SourceCheckError::Property(location));
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(namespace))
        .ok_or(SourceCheckError::Property(location))?;
    if !store.set_structured_type_members(type_, Some(exports), Some(properties), None, None, None)
        || !store.set_value_symbol_links(
            namespace,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        )
    {
        return Err(SourceCheckError::Property(location));
    }
    Ok(type_)
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

fn resolve_scoped_jsx_namespace_symbol(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    location: NodeRef,
    name: &str,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let mut current = Some(location);
    let mut found = None;
    while let Some(node) = current {
        found = bound
            .locals(node)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name));
        if found.is_some() {
            break;
        }
        current = arena
            .get(node.node)
            .and_then(|record| record.parent)
            .map(|parent| child_ref(node, parent));
    }
    let Some(symbol) = found.or_else(|| {
        store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source(name))
    }) else {
        return Ok(None);
    };
    let symbol = resolve_local_jsx_namespace_alias(store, symbol, location)?;
    let record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Property(location))?;
    Ok((record.flags().intersects(SymbolFlags::MODULE)
        && record.flags().intersects(SymbolFlags::VALUE))
    .then_some(symbol))
}

fn check_jsx_attributes(
    store: &mut CanonicalTypeMapperStore,
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    expected_attributes: TypeId,
    attributes: &[JsxAttributePlan],
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Vec<CheckedJsxAttribute>, SourceCheckError> {
    let (arena, _, _, _) = source;
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
            JsxAttributeValue::EmptyExpression { wrapper, report } => {
                if *report {
                    add_diagnostic(diagnostics, *wrapper, 17_000, std::iter::empty::<&str>())?;
                }
                publish_type_links(store, *wrapper, namespace.error_type)?;
                namespace.error_type
            }
            JsxAttributeValue::Expression { wrapper, value } => {
                let type_ = execute_scalar(store, source, namespace, value, options, diagnostics)?;
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
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    expected_attributes: TypeId,
    spread: &JsxObjectSpreadPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(Vec<CheckedJsxAttribute>, TypeId), SourceCheckError> {
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
        let value_type = execute_scalar(store, source, namespace, value, options, diagnostics)?;
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

fn check_jsx_source_spread(
    store: &mut CanonicalTypeMapperStore,
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    spread: &JsxSourceSpreadPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Vec<CheckedJsxAttribute>, SourceCheckError> {
    let JsxScalarPlan::Identifier { node, .. } = &spread.value else {
        return Err(unsupported(spread.node, SyntaxKind::JsxSpreadAttribute));
    };
    let type_ = execute_scalar(
        store,
        source,
        namespace,
        &spread.value,
        options,
        diagnostics,
    )?;
    resolve_jsx_spread_members(store, type_, source.3, spread.node)?
        .into_iter()
        .map(|(symbol, type_)| {
            let record = store
                .symbol(symbol)
                .ok_or(SourceCheckError::Property(spread.node))?;
            let name = record
                .name()
                .as_utf8()
                .filter(|name| !name.is_empty())
                .ok_or(SourceCheckError::Property(spread.node))?;
            if !record.flags().contains(SymbolFlags::PROPERTY) {
                return Err(SourceCheckError::Property(spread.node));
            }
            Ok(CheckedJsxAttribute {
                plan: JsxAttributePlan {
                    node: spread.node,
                    name_node: *node,
                    name: name.to_owned(),
                    symbol,
                    value: JsxAttributeValue::ImplicitTrue,
                },
                type_,
            })
        })
        .collect()
}

fn resolve_jsx_spread_members(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
    location: NodeRef,
) -> Result<Vec<(SemanticSymbolId, TypeId)>, SourceCheckError> {
    if validate_direct_generic_reference(store, type_).is_ok() {
        let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
        let members = resolve_members_with_array_targets(store, type_, array_targets)
            .map_err(|_| SourceCheckError::Property(location))?;
        let properties = members.properties().to_vec();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        return properties
            .into_iter()
            .map(|symbol| {
                demand_instantiated_property_type(store, type_, symbol, array_targets, &mut session)
                    .map(|type_| (symbol, type_))
                    .map_err(|_| SourceCheckError::Property(location))
            })
            .collect();
    }

    let properties = store
        .type_payload(type_)
        .and_then(|record| record.data().structured())
        .ok_or_else(|| unsupported(location, SyntaxKind::JsxSpreadAttribute))?
        .properties
        .clone()
        .unwrap_or_default();
    properties
        .into_iter()
        .map(|symbol| {
            store
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .filter(|type_| store.type_payload(*type_).is_some())
                .map(|type_| (symbol, type_))
                .ok_or(SourceCheckError::Property(location))
        })
        .collect()
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
    source: (
        &NodeArena,
        &BoundFile,
        &DeclaredTypeHost<'_>,
        Option<&CanonicalGlobalTypes>,
    ),
    namespace: &JsxNamespace,
    scalar: &JsxScalarPlan,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let (arena, bound, host, _) = source;
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
        JsxScalarPlan::GlobalThis(node) => {
            let symbol = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?
                .global_this_symbol;
            let type_ = store
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .filter(|type_| {
                    store
                        .type_payload(*type_)
                        .is_some_and(|record| record.symbol() == Some(symbol))
                })
                .ok_or(SourceCheckError::Property(*node))?;
            publish_symbol_links(store, *node, symbol)?;
            (*node, type_)
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
                    variable
                        .type_
                        .into_iter()
                        .chain(variable.initializer)
                        .find_map(|node| {
                            store
                                .type_node_links(child_ref(declaration, node))
                                .and_then(|links| links.resolved_type)
                                .filter(|type_| store.type_payload(*type_).is_some())
                        })
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
            let receiver_type =
                execute_scalar(store, source, namespace, receiver, options, diagnostics)?;
            if matches!(receiver.as_ref(), JsxScalarPlan::GlobalThis(_)) {
                let bootstrap =
                    store
                        .intrinsic_bootstrap()
                        .ok_or(SourceCheckError::LiteralCache(
                            SourceLiteralCacheError::BootstrapUninitialized,
                        ))?;
                if name != "state"
                    || store
                        .symbol_table(bootstrap.globals)
                        .is_none_or(|globals| globals.get_source(name).is_some())
                {
                    return Err(unsupported(*node, SyntaxKind::PropertyAccessExpression));
                }
                if options.no_implicit_any {
                    add_diagnostic(diagnostics, *name_node, 7017, ["typeof globalThis"])?;
                }
                (*node, namespace.any_type)
            } else if receiver_type == namespace.any_type || receiver_type == namespace.error_type {
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
                let target = type_to_string_with_host_and_flags(
                    store,
                    host,
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
        JsxScalarPlan::TypeAssertion {
            node,
            type_node,
            value,
        } => {
            execute_scalar(store, source, namespace, value, options, diagnostics)?;
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ))?;
            let asserted = match jsx_node(arena, bound, store, *type_node)?.kind {
                SyntaxKind::AnyKeyword => bootstrap.any_type,
                SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
                kind => return Err(unsupported(*type_node, kind)),
            };
            publish_type_links(store, *type_node, asserted)?;
            (*node, asserted)
        }
        JsxScalarPlan::Parenthesized { node, value } => {
            let type_ = execute_scalar(store, source, namespace, value, options, diagnostics)?;
            (*node, type_)
        }
        JsxScalarPlan::Conditional {
            node,
            condition,
            when_true,
            when_false,
        } => {
            execute_scalar(store, source, namespace, condition, options, diagnostics)?;
            let true_type =
                execute_scalar(store, source, namespace, when_true, options, diagnostics)?;
            let false_type =
                execute_scalar(store, source, namespace, when_false, options, diagnostics)?;
            let type_ = if true_type == false_type {
                true_type
            } else {
                let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
                store.literal_union_type_prepared(&[true_type, false_type], None, &mut prepared)?
            };
            (*node, type_)
        }
        JsxScalarPlan::AdjacentElements { node, left, right } => {
            execute_jsx_element(store, source, namespace, left, options, diagnostics)?;
            let type_ = execute_jsx_element(store, source, namespace, right, options, diagnostics)?;
            (*node, type_)
        }
        JsxScalarPlan::Element(element) => {
            return execute_jsx_element(store, source, namespace, element, options, diagnostics);
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
        let name = checked_jsx_children_name(store, children)?.to_owned();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                EscapedName::source(&name),
            ))
            .ok_or(SourceCheckError::Property(children.node))?;
        if !store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(children.type_),
                ..ValueSymbolLinks::default()
            },
        ) || store
            .insert_symbol(members, EscapedName::source(&name), symbol)
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
        let name = checked_jsx_children_name(store, children)?;
        let symbol = members
            .get_source(name)
            .ok_or(SourceCheckError::Property(node))?;
        let record = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Property(node))?;
        if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some(name)
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
    host: &DeclaredTypeHost<'_>,
    opening: NodeRef,
    tag: &JsxTagPlan,
    (expected, actual): (TypeId, TypeId),
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
    options: CanonicalCheckerOptions,
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
    let children_name = children
        .map(|children| checked_jsx_children_name(store, children).map(str::to_owned))
        .transpose()?;
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
            deferred_react_attribute_type(store, host, expected, attribute, options, diagnostics)?
        {
            type_
        } else if let Some(type_) =
            matching_attribute_index_value_type(store, &index_infos, &attribute.plan.name)?
        {
            type_
        } else if attribute.plan.name.contains('-') {
            continue;
        } else {
            has_excess_attribute = true;
            let target = type_to_string_with_host_and_flags(
                store,
                host,
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
                    format_attribute_object(store, host, attributes, children)?,
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
        let name = children_name
            .as_deref()
            .expect("checked JSX children retain their property name");
        present.insert(name);
        if !children.individual_errors
            && let Some(expected_type) = resolve_expected_jsx_child_type(
                store,
                host,
                expected,
                name,
                opening,
                options,
                diagnostics,
            )?
            && !store.is_type_assignable_to(children.type_, expected_type)?
        {
            let display =
                get_type_names_for_assignability_error(store, children.type_, expected_type)?;
            let explicit_fragment = tag.namespace_member.as_ref().is_some_and(|member| {
                store
                    .symbol(member.member)
                    .and_then(|record| record.name().as_utf8())
                    == Some("Fragment")
            });
            let node = if explicit_fragment
                && let Some(NodeData::JsxExpression(expression)) =
                    host.node(children.node).map(|record| &record.data)
                && let Some(value) = expression.expression
            {
                child_ref(children.node, value)
            } else {
                children.node
            };
            let related_information = if explicit_fragment
                && matches!(
                    validate_stored_callable_set(store, children.type_),
                    StoredCallableSetValidation::Valid { .. }
                ) {
                vec![CanonicalCheckerRelatedInformation {
                    node: Some(node),
                    diagnostic: Diagnostic::new(
                        message_by_code(6212).ok_or(SourceCheckError::MissingDiagnostic(6212))?,
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
                        message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                        [display.source, display.target],
                    ),
                    related_information,
                },
            );
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
                let source = format_attribute_object(store, host, attributes, children)?;
                let target = type_to_string_with_host_and_flags(
                    store,
                    host,
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

fn deferred_react_attribute_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expected: TypeId,
    attribute: &CheckedJsxAttribute,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Option<TypeId>, SourceCheckError> {
    let location = attribute.plan.node;
    let Some(attributes) = deferred_react_class_attributes_base(store, host, expected, location)?
    else {
        return Ok(None);
    };
    let Some(selected) = select_deferred_react_attribute_property(
        store,
        host,
        expected,
        attributes,
        &attribute.plan.name,
        location,
    )?
    else {
        return Ok(None);
    };
    let property = selected.symbol;
    let property_record = store
        .symbol(property)
        .ok_or(SourceCheckError::Property(location))?;
    let [declaration] = property_record
        .declarations()
        .ok_or(SourceCheckError::Property(location))?
    else {
        return Err(SourceCheckError::Property(location));
    };
    let declaration = *declaration;
    let allowed = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT;
    if !property_record.flags().contains(SymbolFlags::PROPERTY)
        || property_record.flags().without(allowed) != SymbolFlags::NONE
        || property_record.check_flags() != CheckFlags::NONE
        || property_record.name().as_utf8() != Some(attribute.plan.name.as_str())
        || property_record.value_declaration() != Some(declaration)
        || property_record.members().is_some()
        || property_record.exports().is_some()
        || property_record.export_symbol().is_some()
        || store.get_parent_of_symbol(property) != Some(selected.owner)
        || !host.symbol_matches(store, declaration, property)
    {
        return Err(SourceCheckError::Property(declaration));
    }
    let annotation = validate_react_attribute_declaration(
        store,
        host,
        selected.owner,
        declaration,
        &attribute.plan.name,
        property_record.flags().contains(SymbolFlags::OPTIONAL),
    )?;
    let cached = match store.value_symbol_links(property) {
        None => None,
        Some(links) if links == &ValueSymbolLinks::default() => None,
        Some(links) => {
            let type_ = links
                .resolved_type
                .filter(|type_| store.type_payload(*type_).is_some())
                .ok_or(SourceCheckError::Property(declaration))?;
            let expected_links = ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            };
            if links != &expected_links
                || store
                    .type_node_links(annotation)
                    .and_then(|links| links.resolved_type)
                    .is_some_and(|resolved| resolved != type_)
            {
                return Err(SourceCheckError::Property(declaration));
            }
            Some(type_)
        }
    };
    if cached.is_none() && !store.try_reserve_value_symbol_links(1) {
        return Err(SourceCheckError::Property(declaration));
    }
    let resolved = CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_type_from_type_node(annotation)?;
    if cached.is_some_and(|cached| cached != resolved) {
        return Err(SourceCheckError::Property(declaration));
    }
    publish_attribute_value_links(store, property, resolved, declaration)?;
    instantiate_deferred_react_attribute_type(store, selected, resolved, declaration).map(Some)
}

fn instantiate_deferred_react_attribute_type(
    store: &CanonicalTypeMapperStore,
    property: DeferredReactAttributeProperty,
    type_: TypeId,
    declaration: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let Some(argument) = property.type_argument else {
        return Ok(type_);
    };
    if !matches!(
        store
            .type_payload(type_)
            .map(super::type_records::TypeRecord::data),
        Some(super::TypeData::TypeParameter(_))
    ) {
        return Ok(type_);
    }
    let parameter = super::declared::cached_ordinary_type_parameter_owner(store, type_)
        .ok_or(SourceCheckError::Property(declaration))?;
    if store.get_parent_of_symbol(parameter) != Some(property.owner) {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(argument)
}

fn select_deferred_react_attribute_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expected: TypeId,
    attributes: SemanticSymbolId,
    name: &str,
    location: NodeRef,
) -> Result<Option<DeferredReactAttributeProperty>, SourceCheckError> {
    let projection = store
        .validate_deferred_intersection_type(expected)
        .map_err(|_| SourceCheckError::Property(location))?;
    let [class_type, element_type] = projection.types.as_slice() else {
        return Err(SourceCheckError::Property(location));
    };
    let [_, element_argument] = projection.alias_arguments.as_slice() else {
        return Err(SourceCheckError::Property(location));
    };
    let class = validate_direct_generic_reference(store, *class_type)
        .map_err(|_| SourceCheckError::Property(location))?;
    let class_owner = store
        .type_payload(class.target)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(SourceCheckError::Property(location))?;
    for (owner, type_argument) in [(class_owner, Some(*element_argument)), (attributes, None)] {
        if let Some(symbol) = react_interface_named_property(store, owner, name, location)? {
            return Ok(Some(DeferredReactAttributeProperty {
                owner,
                symbol,
                type_argument,
            }));
        }
    }

    let element = validate_direct_generic_reference(store, *element_type)
        .map_err(|_| SourceCheckError::Property(location))?;
    let owner = store
        .type_payload(element.target)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(SourceCheckError::Property(location))?;
    let namespace = store
        .get_parent_of_symbol(attributes)
        .ok_or(SourceCheckError::Property(location))?;
    validate_react_html_attribute_owner(store, host, namespace, owner, location)?;
    if element.type_arguments.as_slice() != [*element_argument] {
        return Err(SourceCheckError::Property(location));
    }
    if let Some(symbol) = react_interface_named_property(store, owner, name, location)? {
        return Ok(Some(DeferredReactAttributeProperty {
            owner,
            symbol,
            type_argument: Some(*element_argument),
        }));
    }

    let base = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("HTMLAttributes"))
        .and_then(|base| store.get_merged_symbol(base))
        .ok_or(SourceCheckError::Property(location))?;
    if base == owner {
        return Ok(None);
    }
    validate_react_html_attribute_owner(store, host, namespace, base, location)?;
    validate_react_derived_html_attributes(store, host, owner, base, location)?;
    Ok(
        react_interface_named_property(store, base, name, location)?.map(|symbol| {
            DeferredReactAttributeProperty {
                owner: base,
                symbol,
                type_argument: Some(*element_argument),
            }
        }),
    )
}

fn react_interface_named_property(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    name: &str,
    location: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members))
        .ok_or(SourceCheckError::Property(location))?;
    let Some(symbol) = members.get_source(name) else {
        return Ok(None);
    };
    store
        .get_merged_symbol(symbol)
        .map(Some)
        .ok_or(SourceCheckError::Property(location))
}

fn validate_react_html_attribute_owner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    owner: SemanticSymbolId,
    location: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = store
        .symbol(owner)
        .ok_or(SourceCheckError::Property(location))?;
    let name = record
        .name()
        .as_utf8()
        .ok_or(SourceCheckError::Property(location))?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(SourceCheckError::Property(location))?;
    let exported = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(name))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if !record.flags().contains(SymbolFlags::INTERFACE)
        || record
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || record.check_flags() != CheckFlags::NONE
        || !name.ends_with("HTMLAttributes")
        || record.members().is_none()
        || record.exports().is_some()
        || store.get_parent_of_symbol(owner) != Some(namespace)
        || store.get_merged_symbol(owner) != Some(owner)
        || exported != Some(owner)
    {
        return Err(SourceCheckError::Property(location));
    }
    for declaration in declarations {
        let declaration_record = host
            .node(*declaration)
            .ok_or(SourceCheckError::Property(*declaration))?;
        let NodeData::InterfaceDeclaration(interface) = &declaration_record.data else {
            return Err(SourceCheckError::Property(*declaration));
        };
        if declaration_record.kind != SyntaxKind::InterfaceDeclaration
            || declaration_record.flags.0 != 0
            || !host.symbol_matches(store, *declaration, owner)
            || interface
                .type_parameters
                .as_ref()
                .is_none_or(|parameters| parameters.nodes.len() != 1)
        {
            return Err(SourceCheckError::Property(*declaration));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Base syntax and its generic argument share one identity proof.
fn validate_react_derived_html_attributes(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    derived: SemanticSymbolId,
    base: SemanticSymbolId,
    location: NodeRef,
) -> Result<(), SourceCheckError> {
    let owner = store
        .symbol(derived)
        .ok_or(SourceCheckError::Property(location))?;
    let [declaration] = owner
        .declarations()
        .ok_or(SourceCheckError::Property(location))?
    else {
        return Err(SourceCheckError::Property(location));
    };
    let declaration = *declaration;
    let record = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(declaration))?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(SourceCheckError::Property(declaration));
    };
    let clauses = interface
        .heritage_clauses
        .as_ref()
        .ok_or(SourceCheckError::Property(declaration))?;
    let [clause] = clauses.nodes.as_slice() else {
        return Err(SourceCheckError::Property(declaration));
    };
    let clause = child_ref(declaration, *clause);
    let clause_record = host
        .node(clause)
        .ok_or(SourceCheckError::Property(clause))?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(SourceCheckError::Property(clause));
    };
    let [reference] = heritage.types.nodes.as_slice() else {
        return Err(SourceCheckError::Property(clause));
    };
    let reference = child_ref(clause, *reference);
    let reference_record = host
        .node(reference)
        .ok_or(SourceCheckError::Property(reference))?;
    let NodeData::ExpressionWithTypeArguments(expression) = &reference_record.data else {
        return Err(SourceCheckError::Property(reference));
    };
    let name = child_ref(reference, expression.expression);
    let name_record = host.node(name).ok_or(SourceCheckError::Property(name))?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(SourceCheckError::Property(name));
    };
    let arguments = expression
        .type_arguments
        .as_ref()
        .ok_or(SourceCheckError::Property(reference))?;
    let [argument] = arguments.nodes.as_slice() else {
        return Err(SourceCheckError::Property(reference));
    };
    let argument = child_ref(reference, *argument);
    let argument_record = host
        .node(argument)
        .ok_or(SourceCheckError::Property(argument))?;
    let NodeData::TypeReferenceNode(argument_type) = &argument_record.data else {
        return Err(SourceCheckError::Property(argument));
    };
    let parameter = child_ref(argument, argument_type.type_name);
    let parameter_record = host
        .node(parameter)
        .ok_or(SourceCheckError::Property(parameter))?;
    let NodeData::Identifier(parameter_name) = &parameter_record.data else {
        return Err(SourceCheckError::Property(parameter));
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.has_trailing_comma
        || reference_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || reference_record.flags.0 != 0
        || reference_record.parent != Some(clause.node)
        || expression.facts != 0
        || arguments.has_trailing_comma
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(reference.node)
        || identifier.flow_node.is_some()
        || identifier.text != "HTMLAttributes"
        || argument_record.kind != SyntaxKind::TypeReference
        || argument_record.flags.0 != 0
        || argument_record.parent != Some(reference.node)
        || argument_type.type_arguments.is_some()
        || parameter_record.kind != SyntaxKind::Identifier
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(argument.node)
        || parameter_name.flow_node.is_some()
    {
        return Err(SourceCheckError::Property(declaration));
    }
    let mut resolver = host.name_resolver_host(store)?;
    let resolved_base = resolver
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(super::DeclaredTypeError::from)?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let resolved_parameter = resolver
        .resolve_entity_name(parameter, SymbolFlags::TYPE)
        .map_err(super::DeclaredTypeError::from)?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let expected_parameter = owner
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(&parameter_name.text))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if resolved_base != Some(base)
        || resolved_parameter.is_none()
        || resolved_parameter != expected_parameter
    {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(())
}

fn deferred_react_class_attributes_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expected: TypeId,
    location: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let record = store
        .type_payload(expected)
        .ok_or(SourceCheckError::Property(location))?;
    if record.flags() != TypeFlags::INTERSECTION {
        return Ok(None);
    }
    let projection = store
        .validate_deferred_intersection_type(expected)
        .map_err(|_| SourceCheckError::Property(location))?;
    let Some(alias) = projection.alias_symbol else {
        return Ok(None);
    };
    let alias_record = store
        .symbol(alias)
        .ok_or(SourceCheckError::Property(location))?;
    if alias_record.name().as_utf8() != Some("DetailedHTMLProps") {
        return Ok(None);
    }
    let namespace = store
        .get_parent_of_symbol(alias)
        .ok_or(SourceCheckError::Property(location))?;
    let namespace_record = store
        .symbol(namespace)
        .ok_or(SourceCheckError::Property(location))?;
    if namespace_record.name().as_utf8() != Some("React") {
        return Ok(None);
    }
    let exports = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Property(location))?;
    let [class_reference, attributes_reference] = projection.types.as_slice() else {
        return Err(SourceCheckError::Property(location));
    };
    let [attributes_argument, target_argument] = projection.alias_arguments.as_slice() else {
        return Err(SourceCheckError::Property(location));
    };
    let reference = validate_direct_generic_reference(store, *class_reference)
        .map_err(|_| SourceCheckError::Property(location))?;
    let class = store
        .type_payload(reference.target)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(SourceCheckError::Property(location))?;
    let attributes = exports
        .get_source("Attributes")
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Property(location))?;
    let class_record = store
        .symbol(class)
        .ok_or(SourceCheckError::Property(location))?;
    let attributes_record = store
        .symbol(attributes)
        .ok_or(SourceCheckError::Property(location))?;
    let interface_flags = SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT;
    if !alias_record.flags().contains(SymbolFlags::TYPE_ALIAS)
        || alias_record
            .flags()
            .without(SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || store.get_merged_symbol(alias) != Some(alias)
        || exports
            .get_source("DetailedHTMLProps")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(alias)
        || *attributes_reference != *attributes_argument
        || reference.type_arguments.as_slice() != [*target_argument]
        || !class_record.flags().contains(SymbolFlags::INTERFACE)
        || class_record.flags().without(interface_flags) != SymbolFlags::NONE
        || class_record.name().as_utf8() != Some("ClassAttributes")
        || store.get_parent_of_symbol(class) != Some(namespace)
        || exports
            .get_source("ClassAttributes")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(class)
        || !attributes_record.flags().contains(SymbolFlags::INTERFACE)
        || attributes_record.flags().without(interface_flags) != SymbolFlags::NONE
        || attributes_record.check_flags() != CheckFlags::NONE
        || attributes_record.name().as_utf8() != Some("Attributes")
        || attributes_record
            .declarations()
            .is_none_or(<[NodeRef]>::is_empty)
        || attributes_record.members().is_none()
        || attributes_record.exports().is_some()
        || store.get_parent_of_symbol(attributes) != Some(namespace)
    {
        return Err(SourceCheckError::Property(location));
    }
    validate_react_class_attributes_heritage(store, host, class, attributes, location)?;
    Ok(Some(attributes))
}

fn validate_react_class_attributes_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    class: SemanticSymbolId,
    attributes: SemanticSymbolId,
    location: NodeRef,
) -> Result<(), SourceCheckError> {
    let owner = store
        .symbol(class)
        .ok_or(SourceCheckError::Property(location))?;
    let [declaration] = owner
        .declarations()
        .ok_or(SourceCheckError::Property(location))?
    else {
        return Err(SourceCheckError::Property(location));
    };
    let declaration = *declaration;
    let record = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(declaration))?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(SourceCheckError::Property(declaration));
    };
    let clauses = interface
        .heritage_clauses
        .as_ref()
        .ok_or(SourceCheckError::Property(declaration))?;
    let [clause] = clauses.nodes.as_slice() else {
        return Err(SourceCheckError::Property(declaration));
    };
    let clause = child_ref(declaration, *clause);
    let clause_record = host
        .node(clause)
        .ok_or(SourceCheckError::Property(clause))?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(SourceCheckError::Property(clause));
    };
    let [base] = heritage.types.nodes.as_slice() else {
        return Err(SourceCheckError::Property(clause));
    };
    let base = child_ref(clause, *base);
    let base_record = host.node(base).ok_or(SourceCheckError::Property(base))?;
    let NodeData::ExpressionWithTypeArguments(expression) = &base_record.data else {
        return Err(SourceCheckError::Property(base));
    };
    let name = child_ref(base, expression.expression);
    let name_record = host.node(name).ok_or(SourceCheckError::Property(name))?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(SourceCheckError::Property(name));
    };
    if record.kind != SyntaxKind::InterfaceDeclaration
        || record.flags.0 != 0
        || !host.symbol_matches(store, declaration, class)
        || clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.has_trailing_comma
        || base_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || base_record.flags.0 != 0
        || base_record.parent != Some(clause.node)
        || expression.type_arguments.is_some()
        || expression.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(base.node)
        || identifier.flow_node.is_some()
        || identifier.text != "Attributes"
    {
        return Err(SourceCheckError::Property(declaration));
    }
    let resolved = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(super::DeclaredTypeError::from)?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if resolved != Some(attributes) {
        return Err(SourceCheckError::Property(declaration));
    }
    Ok(())
}

fn validate_react_attribute_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    attributes: SemanticSymbolId,
    declaration: NodeRef,
    expected_name: &str,
    expected_optional: bool,
) -> Result<NodeRef, SourceCheckError> {
    let record = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(declaration))?;
    let (name, annotation, postfix) = match &record.data {
        NodeData::PropertyDeclaration(property)
            if record.kind == SyntaxKind::PropertyDeclaration
                && property.initializer.is_none()
                && property.symbol.is_none()
                && property.facts == 0 =>
        {
            (
                property.name,
                property
                    .type_
                    .ok_or(SourceCheckError::Property(declaration))?,
                property.postfix_token,
            )
        }
        NodeData::PropertySignatureDeclaration(property)
            if record.kind == SyntaxKind::PropertySignature && property.symbol.is_none() =>
        {
            (property.name, property.type_, property.postfix_token)
        }
        _ => return Err(SourceCheckError::Property(declaration)),
    };
    let interface = record
        .parent
        .map(|parent| child_ref(declaration, parent))
        .ok_or(SourceCheckError::Property(declaration))?;
    let interface_record = host
        .node(interface)
        .ok_or(SourceCheckError::Property(interface))?;
    let NodeData::InterfaceDeclaration(interface_data) = &interface_record.data else {
        return Err(SourceCheckError::Property(interface));
    };
    let name = child_ref(declaration, name);
    let (actual_name, _) = jsx_namespace_property_name(host, declaration, name)?;
    let annotation = child_ref(declaration, annotation);
    let annotation_record = host
        .node(annotation)
        .ok_or(SourceCheckError::Property(annotation))?;
    if record.flags.0 != 0
        || interface_record.kind != SyntaxKind::InterfaceDeclaration
        || !host.symbol_matches(store, interface, attributes)
        || !interface_data.members.nodes.contains(&declaration.node)
        || actual_name != expected_name
        || annotation_record.parent != Some(declaration.node)
        || postfix.is_some() != expected_optional
    {
        return Err(SourceCheckError::Property(declaration));
    }
    if let Some(postfix) = postfix {
        let postfix = child_ref(declaration, postfix);
        let token = host
            .node(postfix)
            .ok_or(SourceCheckError::Property(postfix))?;
        if token.kind != SyntaxKind::QuestionToken
            || token.flags.0 != 0
            || token.parent != Some(declaration.node)
        {
            return Err(SourceCheckError::Property(postfix));
        }
    }
    Ok(annotation)
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
            "{}: {};",
            checked_jsx_children_name(store, children)?,
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

fn checked_jsx_children_name(
    store: &CanonicalTypeMapperStore,
    children: CheckedJsxChildren,
) -> Result<&str, SourceCheckError> {
    children.name.map_or(Ok("children"), |symbol| {
        store
            .symbol(symbol)
            .and_then(|record| record.name().as_utf8())
            .ok_or(SourceCheckError::Property(children.node))
    })
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
    use ts_parser::{
        ParseResult, parse_javascript_source_file, parse_jsx_source_file, parse_source_file,
    };

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, IntrinsicBootstrapOptions, SourceFileLinks,
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
            Self::build(source, file, false, false)
        }

        fn recovering(source: &str, file: FileId) -> Self {
            Self::build(source, file, true, false)
        }

        fn recovering_javascript(source: &str, file: FileId) -> Self {
            Self::build(source, file, true, true)
        }

        fn build(
            source: &str,
            file: FileId,
            allow_parser_diagnostics: bool,
            javascript: bool,
        ) -> Self {
            let parsed = if javascript {
                parse_javascript_source_file(source)
            } else {
                parse_jsx_source_file(source)
            };
            if !allow_parser_diagnostics {
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            }
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(if javascript {
                            "\"/project/runtime.js\""
                        } else {
                            "\"/project/runtime.tsx\""
                        }),
                        if javascript {
                            CanonicalSourceLanguage::JavaScript
                        } else {
                            CanonicalSourceLanguage::TypeScript
                        },
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            if javascript {
                binder
                    .bind_javascript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            } else {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
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

    struct ReactFragmentFixture {
        parsed: &'static ParseResult,
        file: FileId,
        context: crate::semantic::CanonicalCheckerContext<'static>,
    }

    impl ReactFragmentFixture {
        fn new(source: &str, file: FileId, runtime: CanonicalJsxRuntime) -> Self {
            let library: &'static ParseResult = Box::leak(Box::new(parse_source_file(concat!(
                "declare namespace React { ",
                "interface ReactElement { marker: string; } ",
                "type ReactNode = ReactElement | string | number | boolean | null | undefined; ",
                "interface ExoticComponent<P = {}> { (props: P): JSX.Element; } ",
                "const Fragment: ExoticComponent<{ children?: ReactNode; }>; ",
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement {} ",
                "interface ElementChildrenAttribute { children: {}; } ",
                "interface IntrinsicElements { ",
                "main: { children?: React.ReactNode; }; div: {}; span: {}; ",
                "} }",
            ))));
            let parsed: &'static ParseResult = Box::leak(Box::new(parse_jsx_source_file(source)));
            assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let library_file = FileId::new(u32::try_from(file.index()).unwrap() + 1_000);
            let mut binder = CanonicalBinder::new();
            for (parsed, current, declaration) in
                [(library, library_file, true), (parsed, file, false)]
            {
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        current,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(format!(
                                "\"/project/react-fragment-{}.tsx\"",
                                current.index(),
                            )),
                            CanonicalSourceLanguage::TypeScript,
                            declaration,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, current)
                    .unwrap();
            }
            let mut options = CanonicalCheckerOptions {
                jsx_runtime: runtime,
                ..CanonicalCheckerOptions::default()
            };
            options.intrinsic.strict_null_checks = true;
            let context = crate::semantic::CanonicalCheckerContext::new(
                binder.finish(),
                vec![(library_file, &library.arena), (file, &parsed.arena)],
                options,
            )
            .unwrap();
            Self {
                parsed,
                file,
                context,
            }
        }

        fn text(&self, node: NodeRef) -> &str {
            let range = self.parsed.arena.get(node.node).unwrap().range;
            self.parsed
                .arena
                .source_text()
                .unwrap()
                .get(range.start.get() as usize..range.end.get() as usize)
                .unwrap()
        }
    }

    #[test]
    fn jsx_unknown_assertion_children_keep_exact_ts2322_and_warm_identity() {
        for (index, runtime) in [CanonicalJsxRuntime::Classic, CanonicalJsxRuntime::Preserve]
            .into_iter()
            .enumerate()
        {
            let mut fixture = ReactFragmentFixture::new(
                "const view = (<main>{(<div />) as unknown}<span /></main>);",
                FileId::new(8_190 + u32::try_from(index).unwrap()),
                runtime,
            );

            fixture.context.check_source_file(fixture.file).unwrap();

            let [diagnostic] = fixture.context.diagnostics().as_slice() else {
                panic!("the unknown JSX child must produce exactly one diagnostic")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'unknown' is not assignable to type 'ReactNode'.",
            );
            assert_eq!(
                fixture.text(diagnostic.node.unwrap()),
                "{(<div />) as unknown}",
            );
            let unknown = fixture
                .context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .unknown_type;
            for (node, record) in fixture.parsed.arena.iter() {
                if matches!(
                    record.kind,
                    SyntaxKind::AsExpression | SyntaxKind::UnknownKeyword
                ) {
                    let node = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                    assert_eq!(
                        fixture
                            .context
                            .store()
                            .type_node_links(node)
                            .and_then(|links| links.resolved_type),
                        Some(unknown),
                    );
                }
            }
            let warm = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
                fixture.context.diagnostics().as_slice().to_vec(),
            );
            fixture.context.recheck_source_file(fixture.file).unwrap();
            assert_eq!(
                (
                    fixture.context.store().type_len(),
                    fixture.context.store().symbol_len(),
                    fixture.context.store().signature_len(),
                    fixture.context.store().checker_link_allocated_lengths(),
                    fixture.context.diagnostics().as_slice().to_vec(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn classic_react_fragments_preserve_shorthand_and_member_child_diagnostics() {
        let mut fixture = ReactFragmentFixture::new(
            concat!(
                "const test = () => \"ready\"; ",
                "const shorthand = <>{test}</>; ",
                "const explicit = <React.Fragment>{test}</React.Fragment>;",
            ),
            FileId::new(8_192),
            CanonicalJsxRuntime::Classic,
        );

        fixture.context.check_source_file(fixture.file).unwrap();

        let [shorthand, explicit] = fixture.context.diagnostics().as_slice() else {
            panic!("both React fragment forms must reject the callable child")
        };
        assert_eq!(shorthand.diagnostic.code(), 2322);
        assert_eq!(fixture.text(shorthand.node.unwrap()), "<>");
        assert_eq!(
            shorthand.diagnostic.render().unwrap(),
            concat!(
                "Type '{ children: () => string; }' is not assignable to type ",
                "'{ children?: ReactNode; }'.\n",
                "  Types of property 'children' are incompatible.\n",
                "    Type '() => string' is not assignable to type 'ReactNode'.",
            ),
        );
        assert!(shorthand.related_information.is_empty());
        assert_eq!(explicit.diagnostic.code(), 2322);
        assert_eq!(fixture.text(explicit.node.unwrap()), "test");
        assert_eq!(
            explicit.diagnostic.render().unwrap(),
            "Type '() => string' is not assignable to type 'ReactNode'.",
        );
        let [related] = explicit.related_information.as_slice() else {
            panic!("the explicit fragment must suggest calling its child")
        };
        assert_eq!(related.diagnostic.code(), 6212);
        assert_eq!(fixture.text(related.node.unwrap()), "test");

        let globals = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .globals;
        let namespace = fixture
            .context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .unwrap();
        let fragment = fixture
            .context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Fragment"))
            .unwrap();
        for (node, record) in fixture.parsed.arena.iter() {
            if record.kind != SyntaxKind::PropertyAccessExpression {
                continue;
            }
            let access = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
            let NodeData::PropertyAccessExpression(property) = &record.data else {
                unreachable!("the fragment tag must retain its namespace member")
            };
            let receiver = child_ref(access, property.expression);
            let member = child_ref(access, property.name);
            assert_eq!(
                fixture
                    .context
                    .store()
                    .symbol_node_links(receiver)
                    .and_then(|links| links.resolved_symbol),
                Some(namespace),
            );
            for node in [access, member] {
                assert_eq!(
                    fixture
                        .context
                        .store()
                        .symbol_node_links(node)
                        .and_then(|links| links.resolved_symbol),
                    Some(fragment),
                );
            }
        }
        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().checker_link_allocated_lengths(),
            fixture.context.diagnostics().as_slice().to_vec(),
        );
        fixture.context.recheck_source_file(fixture.file).unwrap();
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
                fixture.context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn preserve_runtime_does_not_resolve_the_shorthand_fragment_factory() {
        let mut fixture = ReactFragmentFixture::new(
            concat!(
                "const test = () => \"ready\"; ",
                "const shorthand = <>{test}</>;",
            ),
            FileId::new(8_193),
            CanonicalJsxRuntime::Preserve,
        );

        fixture.context.check_source_file(fixture.file).unwrap();

        assert!(fixture.context.diagnostics().is_empty());
        let globals = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .globals;
        let namespace = fixture
            .context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .unwrap();
        let fragment = fixture
            .context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Fragment"))
            .unwrap();
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(fragment)
                .is_none()
        );
    }

    #[test]
    fn react_fragment_member_tags_reject_forged_namespace_ownership() {
        let mut fixture = ReactFragmentFixture::new(
            "const explicit = <React.Fragment />;",
            FileId::new(8_194),
            CanonicalJsxRuntime::Classic,
        );
        let globals = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .globals;
        let namespace = fixture
            .context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .unwrap();
        let fragment = fixture
            .context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Fragment"))
            .unwrap();
        assert!(
            fixture
                .context
                .store_mut_for_test()
                .set_symbol_relationships(fragment, None, None, None, None,)
        );
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            fixture.context.check_source_file(fixture.file),
            Err(SourceCheckError::Property(_))
        ));
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep imported aliases and foreign index identity together.
    fn imported_factory_jsx_namespace_preserves_cross_file_index_identity() {
        let library = parse_source_file(concat!(
            "function createElement(element: string, props: any): any {}\n",
            "namespace JSX { export interface IntrinsicElements { [key: string]: any; } }\n",
            "export { createElement, JSX };\n",
        ));
        let consumer = parse_jsx_source_file(concat!(
            "import * as MyLib from './library';\n",
            "const content = <custom-element />;\n",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(
            consumer.diagnostics.is_empty(),
            "{:?}",
            consumer.diagnostics
        );
        let library_file = FileId::new(8_160);
        let consumer_file = FileId::new(8_161);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (&library, library_file, "\"/project/library.ts\""),
            (&consumer, consumer_file, "\"/project/index.tsx\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let library_bound = files.remove(&library_file).unwrap();
        let consumer_bound = files.remove(&consumer_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&library.arena, library.source_file, library_file)
            .unwrap();
        let source = store
            .register_source_file(&consumer.arena, consumer.source_file, consumer_file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();

        let module = library_bound.symbol(library_bound.source_file()).unwrap();
        let import = consumer_bound
            .locals(consumer_bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("MyLib"))
            .unwrap();
        let namespace = library_bound
            .locals(library_bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let exported = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("JSX"))
            .unwrap();
        for (alias, target) in [(import, module), (exported, namespace)] {
            assert!(store.set_alias_symbol_links(
                alias,
                AliasSymbolLinks {
                    immediate_target: Some(target),
                    alias_target: AliasTargetState::Resolved(target),
                    ..AliasSymbolLinks::default()
                },
            ));
        }
        assert!(store.set_source_file_links(
            source,
            SourceFileLinks {
                local_jsx_namespace: "MyLib".to_owned(),
                ..SourceFileLinks::default()
            },
        ));
        let opening = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::JsxSelfClosingElement).then_some(NodeRef::new(
                    consumer.arena.id(),
                    consumer_file,
                    node,
                ))
            })
            .unwrap();
        let host = DeclaredTypeHost::new([
            (&library.arena, &library_bound),
            (&consumer.arena, &consumer_bound),
        ])
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        store
            .check_jsx_element(
                &host,
                opening,
                CanonicalCheckerOptions {
                    no_implicit_any: true,
                    ..CanonicalCheckerOptions::default()
                },
                &mut diagnostics,
            )
            .unwrap();

        assert!(diagnostics.is_empty());
        let symbol = store
            .symbol_node_links(opening)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        let index = store.symbol(symbol).unwrap();
        assert_eq!(
            index
                .value_declaration()
                .map(|declaration| declaration.file),
            Some(library_file),
        );
        assert_eq!(
            store.jsx_element_links(opening).unwrap().jsx_flags,
            JsxFlags::INTRINSIC_INDEXED_ELEMENT,
        );
        let warm = (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
        );
        store
            .check_jsx_element(
                &host,
                opening,
                CanonicalCheckerOptions {
                    no_implicit_any: true,
                    ..CanonicalCheckerOptions::default()
                },
                &mut diagnostics,
            )
            .unwrap();
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn factory_without_local_jsx_namespace_falls_back_to_global_namespace() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace MyLib { export interface Other {} }\n",
                "declare namespace JSX { interface IntrinsicElements { div: any; } }\n",
                "const content = <div />;\n",
            ),
            FileId::new(8_162),
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
        let source =
            super::super::SourceFileRef::new(fixture.store.id(), fixture.bound.source_file());
        assert!(fixture.store.set_source_file_links(
            source,
            SourceFileLinks {
                local_jsx_namespace: "MyLib".to_owned(),
                ..SourceFileLinks::default()
            },
        ));
        let expression = fixture.expression("content");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert!(diagnostics.is_empty());
        assert_eq!(
            fixture
                .store
                .jsx_element_links(expression)
                .unwrap()
                .jsx_flags,
            JsxFlags::INTRINSIC_NAMED_ELEMENT,
        );
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
    #[allow(clippy::too_many_lines)] // Keep mapped, inherited, and JSX index identities together.
    fn inherited_record_intrinsics_keep_the_mapped_index_unmodified() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: T };\n",
                "declare namespace JSX {\n",
                "  interface IntrinsicElements extends Record<string, any> {}\n",
                "}\n",
                "const first = <a />;\n",
                "const second = <b />;\n",
            ),
            FileId::new(8_136),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        for name in ["Record", "JSX"] {
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
        let namespace = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("JSX"))
            .unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture
            .store
            .check_jsx_element(
                &host,
                first,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();

        let type_ = fixture
            .store
            .declared_type_links(intrinsics)
            .and_then(|links| links.declared_type)
            .unwrap();
        let super::super::TypeData::Interface(interface) =
            fixture.store.type_payload(type_).unwrap().data()
        else {
            unreachable!("IntrinsicElements retains its declared interface")
        };
        assert!(interface.declared_index_infos.is_none());
        let [base] = interface.resolved_base_types.as_deref().unwrap() else {
            panic!("IntrinsicElements retains its authenticated Record base")
        };
        let [derived_index] = interface
            .reference
            .object
            .structured
            .index_infos
            .as_deref()
            .unwrap()
        else {
            panic!("IntrinsicElements exposes one inherited string index")
        };
        let derived_index = *derived_index;
        let super::super::TypeData::Mapped(mapped) =
            fixture.store.type_payload(*base).unwrap().data()
        else {
            unreachable!("the inherited base is an authenticated mapped Record")
        };
        let [mapped_index] = mapped.object.structured.index_infos.as_deref().unwrap() else {
            panic!("Record<string, any> owns one string index")
        };
        let mapped_index = *mapped_index;
        assert_ne!(derived_index, mapped_index);
        let original = fixture.store.index_info(mapped_index).unwrap();
        let inherited = fixture.store.index_info(derived_index).unwrap();
        assert!(original.index_symbol().is_none());
        let symbol = inherited.index_symbol().unwrap();
        assert_eq!(
            fixture
                .store
                .jsx_element_links(first)
                .map(|links| links.jsx_flags),
            Some(JsxFlags::INTRINSIC_INDEXED_ELEMENT),
        );

        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.mapper_len(),
            fixture.store.index_info_len(),
        );
        fixture
            .store
            .check_jsx_element(
                &host,
                first,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.mapper_len(),
                fixture.store.index_info_len(),
            ),
            cold,
        );
        fixture
            .store
            .check_jsx_element(
                &host,
                second,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert_eq!(
            fixture
                .store
                .index_info(derived_index)
                .and_then(super::super::signatures::IndexInfo::index_symbol),
            Some(symbol),
        );
        assert!(
            fixture
                .store
                .index_info(mapped_index)
                .unwrap()
                .index_symbol()
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn record_intrinsics_reject_non_string_keys_before_publication() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: T };\n",
                "declare namespace JSX {\n",
                "  interface IntrinsicElements extends Record<number, any> {}\n",
                "}\n",
                "const view = <a />;\n",
            ),
            FileId::new(8_137),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        for name in ["Record", "JSX"] {
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
        let expression = fixture.expression("view");
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.mapper_len(),
            fixture.store.index_info_len(),
        );

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
                kind: SyntaxKind::NumberKeyword,
                ..
            })
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.mapper_len(),
                fixture.store.index_info_len(),
            ),
            before,
        );
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
    fn intrinsic_element_keeps_inherited_element_base_cold() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace React { interface ReactElement<Props, Kind> {} }\n",
                "declare namespace JSX {\n",
                "  interface Element extends React.ReactElement<any, any> {}\n",
                "  interface IntrinsicElements { div: any; }\n",
                "}\n",
                "const view = <div />;\n",
            ),
            FileId::new(8_136),
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
        let react = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .unwrap();
        let react_exports = fixture.store.symbol(react).unwrap().exports().unwrap();
        let react_element = fixture
            .store
            .symbol_table(react_exports)
            .and_then(|exports| exports.get_source("ReactElement"))
            .unwrap();
        let jsx = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("JSX"))
            .unwrap();
        let jsx_exports = fixture.store.symbol(jsx).unwrap().exports().unwrap();
        let element = fixture
            .store
            .symbol_table(jsx_exports)
            .and_then(|exports| exports.get_source("Element"))
            .unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(jsx_exports)
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
        assert!(fixture.store.declared_type_links(intrinsics).is_some());
        assert!(fixture.store.declared_type_links(react_element).is_none());

        let warm = (
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
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep lazy members, warm publication, and TS2558 ranges together.
    fn intrinsic_members_resolve_only_requested_tags_and_keep_type_argument_ranges() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface IntrinsicElements {\n",
            "    unused: Missing;\n",
            "    div: any;\n",
            "    span: any;\n",
            "    component: { (props: { label: string }): any };\n",
            "  }\n",
            "}\n",
            "const first = <div<   number> />;\n",
            "const second = <div<\n    number> />;\n",
            "const third = <span />;\n",
        );
        let mut fixture = RuntimeFixture::new(source, FileId::new(8_151));
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
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let members = fixture.store.symbol(intrinsics).unwrap().members().unwrap();
        let symbols = ["unused", "div", "span", "component"].map(|name| {
            fixture
                .store
                .symbol_table(members)
                .and_then(|members| members.get_source(name))
                .unwrap()
        });
        let first = fixture.expression("first");
        let second = fixture.expression("second");
        let third = fixture.expression("third");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(first, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        let intrinsic_type = fixture
            .store
            .declared_type_links(intrinsics)
            .and_then(|links| links.declared_type)
            .unwrap();
        let structured = fixture
            .store
            .type_payload(intrinsic_type)
            .and_then(|record| record.data().structured())
            .unwrap();
        assert_eq!(structured.members, Some(members));
        assert_eq!(structured.properties.as_deref(), Some(symbols.as_slice()));
        assert!(fixture.store.value_symbol_links(symbols[0]).is_none());
        assert!(fixture.store.value_symbol_links(symbols[1]).is_some());
        assert!(fixture.store.value_symbol_links(symbols[2]).is_none());
        let callable = fixture
            .store
            .value_symbol_links(symbols[3])
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .type_payload(callable)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .map(<[SignatureId]>::len),
            Some(1),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        fixture.check(first, CanonicalJsxRuntime::Preserve, &mut diagnostics);
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

        fixture.check(second, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        fixture.check(third, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(diagnostics.len(), 2);
        for diagnostic in diagnostics.as_slice() {
            assert_eq!(diagnostic.diagnostic.code(), 2558);
            let range = diagnostic.range_override.unwrap().range();
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(&source[start..end], "number");
        }
        assert!(fixture.store.value_symbol_links(symbols[0]).is_none());
        assert!(fixture.store.value_symbol_links(symbols[2]).is_some());
        assert_eq!(
            fixture
                .store
                .declared_type_links(intrinsics)
                .and_then(|links| links.declared_type),
            Some(intrinsic_type),
        );
    }

    #[test]
    fn lazy_intrinsic_members_reject_malformed_unrequested_value_links() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { div: any; span: any; }\n",
                "}\n",
                "const view = <div />;\n",
            ),
            FileId::new(8_152),
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
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let members = fixture.store.symbol(intrinsics).unwrap().members().unwrap();
        let span = fixture
            .store
            .symbol_table(members)
            .and_then(|members| members.get_source("span"))
            .unwrap();
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert!(fixture.store.set_value_symbol_links(
            span,
            ValueSymbolLinks {
                resolved_type: Some(any),
                write_type: Some(any),
                ..ValueSymbolLinks::default()
            },
        ));
        let before = fixture.store.checker_link_allocated_lengths();
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let error = fixture
            .store
            .check_jsx_element(
                &host,
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();

        assert!(matches!(error, SourceCheckError::Property(_)));
        assert_eq!(fixture.store.checker_link_allocated_lengths(), before);
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
    fn intrinsic_element_type_constraints_keep_exact_diagnostics_and_warm_state() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface IntrinsicElements { div: any; span: any; }\n",
            "  type ElementType = 'div';\n",
            "}\n",
            "const valid = <div />;\n",
            "const rejected = <span />;\n",
            "const missing = <ruhroh />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_183);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/element-type.tsx\""),
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

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2786, 2339, 2786],
        );
        for (diagnostic, name) in [(&diagnostics[0], "span"), (&diagnostics[2], "ruhroh")] {
            let node = diagnostic.node.unwrap();
            let NodeData::Identifier(identifier) = &parsed.arena.get(node.node).unwrap().data
            else {
                panic!("the invalid element diagnostic must point to its tag")
            };
            assert_eq!(identifier.text, name);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "'{name}' cannot be used as a JSX component.\n  \
                     Its type '\"{name}\"' is not a valid JSX element type."
                ),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(context.store().intrinsic_bootstrap().unwrap().any_type),
            );
        }
        assert_eq!(
            parsed
                .arena
                .get(diagnostics[1].node.unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::JsxSelfClosingElement,
        );

        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            diagnostics.to_vec(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn generic_element_type_aliases_remain_a_typed_boundary() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface IntrinsicElements { div: any; }\n",
                "  type ElementType<T = any> = T;\n",
                "}\n",
                "const view = <div />;\n",
            ),
            FileId::new(8_184),
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
                kind: SyntaxKind::TypeAliasDeclaration,
                ..
            })
        ));
        assert!(diagnostics.is_empty());
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
    #[allow(clippy::too_many_lines)] // Keep merged React ownership and lazy cache checks together.
    fn augmented_react_attributes_resolve_only_the_requested_namespaced_property() {
        let dom = parse_source_file(concat!(
            "interface HTMLDivElement { align: string; } ",
            "interface HTMLImageElement { src: string; }",
        ));
        let react = parse_source_file(concat!(
            "declare module 'react' { ",
            "export = React; ",
            "namespace React { ",
            "interface DOMAttributes<T> {} ",
            "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
            "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
            "interface ImgHTMLAttributes<T> extends HTMLAttributes<T> { ",
            "src?: string; alt?: MissingImage; ",
            "} ",
            "interface Attributes { key?: MissingKey; } ",
            "interface ClassAttributes<T> extends Attributes { ref?: T; } ",
            "type DetailedHTMLProps<E extends HTMLAttributes<T>, T> = ClassAttributes<T> & E; ",
            "} ",
            "global { namespace JSX { interface IntrinsicElements { ",
            "div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>; ",
            "img: React.DetailedHTMLProps<React.ImgHTMLAttributes<HTMLImageElement>, HTMLImageElement>; ",
            "} } } ",
            "}",
        ));
        let consumer = parse_jsx_source_file(concat!(
            "declare module 'react' { interface Attributes { ",
            "[key: `do-${string}`]: MissingIndex; ",
            "'ns:thing'?: string; ",
            "} } ",
            "export const tag = <div ns:thing='a' />; ",
            "export const image = <img src='./image.png' />; ",
            "export const inherited = <img id='photo' />; ",
            "export const invalid = <img src={1} />;",
        ));
        let dom_file = FileId::new(8_180);
        let react_file = FileId::new(8_181);
        let consumer_file = FileId::new(8_182);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, declaration, default_library, module_state) in [
            (&dom, dom_file, true, true, CanonicalModuleState::Script),
            (
                &react,
                react_file,
                true,
                false,
                CanonicalModuleState::Script,
            ),
            (
                &consumer,
                consumer_file,
                false,
                false,
                CanonicalModuleState::External,
            ),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/react-jsx-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        default_library,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let dom_bound = files.remove(&dom_file).unwrap();
        let react_bound = files.remove(&react_file).unwrap();
        let consumer_bound = files.remove(&consumer_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [
            (&dom, dom_file),
            (&react, react_file),
            (&consumer, consumer_file),
        ] {
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for bound in [&dom_bound, &react_bound] {
            let locals = bound.locals(bound.source_file()).unwrap();
            let symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(_, symbol)| symbol)
                .collect::<Vec<_>>();
            for symbol in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }
        for augmentation in react_bound.module_augmentations() {
            let name = augmentation.name();
            let declaration = react
                .arena
                .get(name.node)
                .and_then(|record| record.parent)
                .map(|node| NodeRef::new(name.arena, name.file, node))
                .unwrap();
            let NodeData::ModuleDeclaration(module) =
                &react.arena.get(declaration.node).unwrap().data
            else {
                unreachable!("the React fixture has a module augmentation")
            };
            if module.keyword == SyntaxKind::GlobalKeyword {
                let symbol = react_bound.symbol(declaration).unwrap();
                let exports = store.symbol(symbol).unwrap().exports().unwrap();
                store
                    .merge_symbol_table(globals, exports, false, None)
                    .unwrap();
            }
        }
        let react_namespace = react
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    react.arena.get(module.name).map(|record| &record.data),
                    Some(NodeData::Identifier(name)) if name.text == "React"
                )
                .then_some(NodeRef::new(react.arena.id(), react_file, node))
                .and_then(|declaration| react_bound.symbol(declaration))
            })
            .unwrap();
        let augmentation = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::ModuleDeclaration(_))
                    .then_some(NodeRef::new(consumer.arena.id(), consumer_file, node))
                    .and_then(|declaration| consumer_bound.symbol(declaration))
            })
            .unwrap();
        let react_namespace = store
            .merge_symbol(react_namespace, augmentation, false)
            .unwrap();
        let react_exports = store.symbol(react_namespace).unwrap().exports().unwrap();
        let attributes = store
            .symbol_table(react_exports)
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        assert!(
            store
                .symbol(attributes)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
        );
        let attribute_members = store.symbol(attributes).unwrap().members().unwrap();
        let key = store
            .symbol_table(attribute_members)
            .and_then(|members| members.get_source("key"))
            .unwrap();
        let namespaced = store
            .symbol_table(attribute_members)
            .and_then(|members| members.get_source("ns:thing"))
            .unwrap();
        let class = store
            .symbol_table(react_exports)
            .and_then(|exports| exports.get_source("ClassAttributes"))
            .unwrap();
        let html = store
            .symbol_table(react_exports)
            .and_then(|exports| exports.get_source("HTMLAttributes"))
            .unwrap();
        let class_members = store.symbol(class).unwrap().members().unwrap();
        let reference = store
            .symbol_table(class_members)
            .and_then(|members| members.get_source("ref"))
            .unwrap();
        let html_members = store.symbol(html).unwrap().members().unwrap();
        let html_properties = ["id", "title"].map(|name| {
            store
                .symbol_table(html_members)
                .and_then(|members| members.get_source(name))
                .unwrap()
        });
        let image_attributes = store
            .symbol_table(react_exports)
            .and_then(|exports| exports.get_source("ImgHTMLAttributes"))
            .unwrap();
        let image_members = store.symbol(image_attributes).unwrap().members().unwrap();
        let image_properties = ["src", "alt"].map(|name| {
            store
                .symbol_table(image_members)
                .and_then(|members| members.get_source(name))
                .unwrap()
        });
        let template = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TemplateLiteralType).then_some(NodeRef::new(
                    consumer.arena.id(),
                    consumer_file,
                    node,
                ))
            })
            .unwrap();
        let opening_named = |expected: &str| {
            consumer
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &consumer.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        consumer.arena.id(),
                        consumer_file,
                        variable.initializer?,
                    ))
                })
                .unwrap()
        };
        let opening = opening_named("tag");
        let image = opening_named("image");
        let inherited = opening_named("inherited");
        let invalid = opening_named("invalid");
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&dom.arena, &dom_bound),
                (&react.arena, &react_bound),
                (&consumer.arena, &consumer_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        store
            .check_jsx_element(
                &host,
                opening,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();

        assert!(diagnostics.is_empty());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            store.value_symbol_links(namespaced),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            }),
        );
        for property in [key, reference, html_properties[0], html_properties[1]] {
            assert!(store.value_symbol_links(property).is_none());
        }
        assert!(store.type_node_links(template).is_none());
        assert!(store.value_symbol_links(image_properties[0]).is_none());
        assert!(store.value_symbol_links(image_properties[1]).is_none());

        store
            .check_jsx_element(
                &host,
                image,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert!(diagnostics.is_empty());
        assert_eq!(
            store.value_symbol_links(image_properties[0]),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            }),
        );
        for property in [
            key,
            reference,
            html_properties[0],
            html_properties[1],
            image_properties[1],
        ] {
            assert!(store.value_symbol_links(property).is_none());
        }
        assert!(store.type_node_links(template).is_none());

        store
            .check_jsx_element(
                &host,
                inherited,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert!(diagnostics.is_empty());
        assert_eq!(
            store.value_symbol_links(html_properties[0]),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            }),
        );
        for property in [key, reference, html_properties[1], image_properties[1]] {
            assert!(store.value_symbol_links(property).is_none());
        }

        store
            .check_jsx_element(
                &host,
                invalid,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        let expected = store
            .jsx_element_links(opening)
            .and_then(|links| links.resolved_jsx_element_attributes_type)
            .unwrap();
        assert!(store.validate_deferred_intersection_type(expected).is_ok());
        for symbol in [class, html, image_attributes] {
            let type_ = store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap();
            let super::super::TypeData::Interface(interface) =
                store.type_payload(type_).unwrap().data()
            else {
                panic!("React attributes must retain their generic interface identities")
            };
            assert!(!interface.declared_members_resolved);
        }
        let warm = (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        for expression in [opening, image, inherited, invalid] {
            store
                .check_jsx_element(
                    &host,
                    expression,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap();
        }
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                diagnostics.as_slice().to_vec(),
            ),
            warm,
        );
        assert_eq!(
            store.insert_symbol(react_exports, EscapedName::source("Attributes"), class),
            Some(Some(attributes)),
        );
        assert!(matches!(
            deferred_react_class_attributes_base(&store, &host, expected, opening),
            Err(SourceCheckError::Property(node)) if node == opening
        ));
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
    fn adjacent_jsx_attribute_elements_keep_parser_and_checker_diagnostic_order() {
        let source = "const view = <X a=<b/><c/> />;\n";
        let mut fixture = RuntimeFixture::recovering(source, FileId::new(8_138));
        let [parser_diagnostic] = fixture.parsed.diagnostics.as_slice() else {
            panic!("adjacent JSX parents must retain one parser diagnostic")
        };
        assert_eq!(parser_diagnostic.code, Some(2657));
        let expression = fixture.expression("view");
        let binary = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        assert_eq!(
            parser_diagnostic.range,
            fixture.parsed.arena.get(binary.node).unwrap().range,
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2304, 7026, 7026],
        );
        let diagnostic_text = diagnostics
            .as_slice()
            .iter()
            .map(|diagnostic| {
                let node = fixture
                    .parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap();
                source
                    .get(node.range.start.get() as usize..node.range.end.get() as usize)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(diagnostic_text, ["X", "<b/>", "<c/>"]);
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            fixture
                .store
                .type_node_links(binary)
                .and_then(|links| links.resolved_type),
            Some(error_type),
        );
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            diagnostics.as_slice().to_vec(),
        );
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                diagnostics.as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    fn conflict_marker_missing_closing_tag_checks_only_the_opening_intrinsic() {
        let source = "const view = <div>\n<<<<<<< HEAD";
        let mut fixture = RuntimeFixture::recovering(source, FileId::new(8_139));
        assert_eq!(
            fixture
                .parsed
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(1005), Some(1185)],
        );
        let expression = fixture.expression("view");
        let NodeData::JsxElement(element) =
            &fixture.parsed.arena.get(expression.node).unwrap().data
        else {
            unreachable!("the source contains an unclosed JSX element")
        };
        let closing = child_ref(expression, element.closing_element);
        let NodeData::JsxClosingElement(close) =
            &fixture.parsed.arena.get(closing.node).unwrap().data
        else {
            unreachable!("the parser retains its synthetic JSX closing element")
        };
        let missing_name = child_ref(closing, close.tag_name);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);

        let [diagnostic] = diagnostics.as_slice() else {
            panic!("only the real JSX opening should produce a semantic diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 7026);
        let opening = fixture
            .parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap();
        assert_eq!(
            source
                .get(opening.range.start.get() as usize..opening.range.end.get() as usize)
                .unwrap(),
            "<div>",
        );
        assert!(fixture.store.symbol_node_links(missing_name).is_none());
        assert!(fixture.store.type_node_links(missing_name).is_none());
        assert!(fixture.store.jsx_element_links(closing).is_none());
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            diagnostics.as_slice().to_vec(),
        );
        fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                diagnostics.as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    fn missing_closing_tag_without_a_conflict_marker_remains_unsupported() {
        let mut fixture = RuntimeFixture::recovering("const view = <div>", FileId::new(8_140));
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
    fn javascript_unary_plus_accepts_only_its_recovered_number_element() {
        let source = "const saved = 'oops';\nconst value = + <number> saved;\n";
        let mut fixture = RuntimeFixture::recovering_javascript(source, FileId::new(8_142));
        assert_eq!(
            fixture
                .parsed
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(17008), Some(1005)],
        );
        let unary = fixture.expression("value");
        let NodeData::PrefixUnaryExpression(prefix) =
            &fixture.parsed.arena.get(unary.node).unwrap().data
        else {
            unreachable!("the fixture contains a unary-plus variable initializer")
        };
        let expression = child_ref(unary, prefix.operand);
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;

        assert_eq!(
            fixture
                .store
                .check_jsx_element(
                    &host,
                    expression,
                    CanonicalCheckerOptions {
                        no_implicit_any: false,
                        ..CanonicalCheckerOptions::default()
                    },
                    &mut diagnostics,
                )
                .unwrap(),
            error_type,
        );
        assert!(diagnostics.is_empty());
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
        );
        fixture
            .store
            .check_jsx_element(
                &host,
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
            ),
            cold,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn javascript_unary_plus_rejects_other_unclosed_intrinsic_tags() {
        let mut fixture = RuntimeFixture::recovering_javascript(
            "const saved = 'oops';\nconst value = + <other> saved;\n",
            FileId::new(8_143),
        );
        let unary = fixture.expression("value");
        let NodeData::PrefixUnaryExpression(prefix) =
            &fixture.parsed.arena.get(unary.node).unwrap().data
        else {
            unreachable!("the fixture contains a unary-plus variable initializer")
        };
        let expression = child_ref(unary, prefix.operand);
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert!(matches!(
            fixture.store.check_jsx_element(
                &host,
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            ),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    kind: SyntaxKind::Identifier,
                    ..
                }
            ))
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn only_the_first_empty_attribute_expression_on_each_opening_is_reported() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare var React: any;\n",
                "const view = <Missing first={} second={} />;\n",
            ),
            FileId::new(8_144),
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
            [2304, 17_000],
        );
        let empty = &diagnostics.as_slice()[1];
        assert_eq!(
            empty.diagnostic.render().unwrap(),
            "JSX attributes must only be assigned a non-empty 'expression'.",
        );
        let range = fixture
            .parsed
            .arena
            .get(empty.node.unwrap().node)
            .unwrap()
            .range;
        assert_eq!(
            fixture
                .parsed
                .arena
                .source_text()
                .unwrap()
                .get(range.start.get() as usize..range.end.get() as usize),
            Some("{}"),
        );
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            diagnostics.as_slice().to_vec(),
        );
        fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                diagnostics.as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The complete fixture proves nested grammar and global-this order.
    fn empty_component_attributes_and_script_this_keep_exact_diagnostics() {
        let source = concat!(
            "declare var React: any;\n",
            "const output = <View>\n",
            "  <ListView refreshControl={\n",
            "    <RefreshControl onRefresh={} refreshing={} />\n",
            "  } dataSource={this.state.ds} renderRow={}>\n",
            "  </ListView>\n",
            "</View>;\n",
        );
        let mut fixture = RuntimeFixture::new(source, FileId::new(8_145));
        let global_this = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let global_this_type = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(global_this))
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            global_this,
            ValueSymbolLinks {
                resolved_type: Some(global_this_type),
                ..ValueSymbolLinks::default()
            },
        ));
        let expression = fixture.expression("output");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);

        let mut ordered = diagnostics.as_slice().iter().collect::<Vec<_>>();
        ordered.sort_by_key(|diagnostic| {
            let range = fixture
                .parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            (range.start, range.end, diagnostic.diagnostic.code())
        });
        assert_eq!(
            ordered
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2304, 2304, 2304, 17_000, 7017, 17_000, 2304, 2304],
        );
        let implicit = ordered
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == 7017)
            .unwrap();
        assert_eq!(
            implicit.diagnostic.render().unwrap(),
            "Element implicitly has an 'any' type because type 'typeof globalThis' \
             has no index signature.",
        );
        let state = fixture
            .parsed
            .arena
            .get(implicit.node.unwrap().node)
            .unwrap();
        assert_eq!(
            source.get(state.range.start.get() as usize..state.range.end.get() as usize),
            Some("state"),
        );
        let this = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ThisKeyword).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        assert_eq!(
            fixture
                .store
                .symbol_node_links(this)
                .and_then(|links| links.resolved_symbol),
            Some(global_this),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(this)
                .and_then(|links| links.resolved_type),
            Some(global_this_type),
        );
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            diagnostics.as_slice().to_vec(),
        );
        fixture.check(expression, CanonicalJsxRuntime::Classic, &mut diagnostics);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                diagnostics.as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    fn ordinary_jsx_comma_expression_remains_unsupported() {
        let mut fixture = RuntimeFixture::new(
            "const view = <Missing value={(<left />, <right />)} />;\n",
            FileId::new(8_141),
        );
        let expression = fixture.expression("view");
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
        );

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
                kind: SyntaxKind::BinaryExpression,
                ..
            })
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
            ),
            before,
        );
        assert!(diagnostics.is_empty());
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
    #[allow(clippy::too_many_lines)] // Both legacy runtimes must retain child links and warm state.
    fn classic_and_preserve_runtimes_use_declared_children_attribute_and_replay_warm() {
        let source = concat!(
            "declare var React: any;\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface ElementChildrenAttribute { offspring: any; }\n",
            "  interface IntrinsicElements { span: { offspring: string }; }\n",
            "}\n",
            "const Box = (props: { offspring: string }) => <span>{props.offspring}</span>;\n",
            "const valid = <Box>ready</Box>;\n",
            "const invalid = <Box>{123}</Box>;\n",
        );

        for (index, runtime) in [CanonicalJsxRuntime::Classic, CanonicalJsxRuntime::Preserve]
            .into_iter()
            .enumerate()
        {
            let parsed = parse_jsx_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_170 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/legacy-children.tsx\""),
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
                    jsx_runtime: runtime,
                    ..CanonicalCheckerOptions::default()
                },
            )
            .unwrap();

            context.check_source_file(file).unwrap();

            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("only the invalid child must fail in {runtime:?} mode")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            let range = parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            assert_eq!(
                source.get(range.start.get() as usize..range.end.get() as usize),
                Some("{123}"),
            );

            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let mut child_properties = 0;
            for (node, record) in parsed.arena.iter() {
                if record.kind != SyntaxKind::JsxAttributes {
                    continue;
                }
                let attributes = NodeRef::new(parsed.arena.id(), file, node);
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
                let child = members.get_source("offspring").unwrap();
                assert!(members.get_source("children").is_none());
                let child_type = context
                    .store()
                    .value_symbol_links(child)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                assert!(
                    child_type == string
                        || context
                            .store()
                            .type_payload(child_type)
                            .unwrap()
                            .flags()
                            .intersects(TypeFlags::NUMBER_LITERAL),
                );
                child_properties += 1;
            }
            assert_eq!(child_properties, 3);

            let cold = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                ),
                cold,
            );
        }
    }

    #[test]
    fn legacy_children_attributes_with_multiple_properties_keep_exact_ts2608_and_warm_state() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface ElementChildrenAttribute { first: any; second: any; }\n",
            "  interface IntrinsicElements { panel: {}; }\n",
            "}\n",
            "const view = <panel>ready</panel>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_172);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/invalid-child-name.tsx\""),
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

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("an ambiguous child property must produce one TS2608 diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2608);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "The global type 'JSX.ElementChildrenAttribute' may not have more than one property.",
        );
        assert_eq!(
            parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::InterfaceDeclaration,
        );

        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep spread ownership, child diagnostics, and warm state together.
    fn identifier_spread_attributes_merge_legacy_children_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface ElementChildrenAttribute { children: any; }\n",
            "  interface IntrinsicElements { div: { locale: string; children: string }; }\n",
            "}\n",
            "interface BaseProps { locale: string; }\n",
            "declare const props: BaseProps;\n",
            "const valid = <div {...props}>ready</div>;\n",
            "const invalid = <div {...props}>{123}</div>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_180);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/jsx-spread-children.tsx\""),
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

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the numeric spread child must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        let range = parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .range;
        assert_eq!(
            source.get(range.start.get() as usize..range.end.get() as usize),
            Some("{123}"),
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let mut spreads = 0;
        for (node, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::JsxAttributes {
                continue;
            }
            let node = NodeRef::new(parsed.arena.id(), file, node);
            let type_ = context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let members = context
                .store()
                .type_payload(type_)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| context.store().symbol_table(members))
                .unwrap();
            let locale = members.get_source("locale").unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(locale)
                    .and_then(|links| links.resolved_type),
                Some(string),
            );
            assert!(members.get_source("children").is_some());
            spreads += 1;
        }
        assert_eq!(spreads, 2);

        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            cold,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve generic source inference and shared signature identity.
    fn generic_jsx_components_infer_identifier_spread_types_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX { interface Element {} }\n",
            "interface Props<T> { value: T; }\n",
            "declare function Widget<T>(props: Props<T>): any;\n",
            "declare const numberProps: Props<number>;\n",
            "const first = <Widget {...numberProps} />;\n",
            "const second = <Widget {...numberProps} />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_181);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-jsx-spread.tsx\""),
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

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let mut signatures = Vec::new();
        for (node, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::JsxSelfClosingElement {
                continue;
            }
            let opening = NodeRef::new(parsed.arena.id(), file, node);
            let signature = context
                .store()
                .signature_links(opening)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .type_parameters()
                    .is_empty()
            );
            signatures.push(signature);
            let NodeData::JsxSelfClosingElement(element) = &record.data else {
                unreachable!("the filtered node is a self-closing JSX element")
            };
            let attributes = child_ref(opening, element.attributes);
            let type_ = context
                .store()
                .type_node_links(attributes)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let value = context
                .store()
                .type_payload(type_)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source("value"))
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(value)
                    .and_then(|links| links.resolved_type),
                Some(number),
            );
        }
        assert_eq!(signatures.len(), 2);
        assert_eq!(signatures[0], signatures[1]);

        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve array identity, child links, and warm-cache checks.
    fn automatic_runtime_combines_multiple_children_with_the_canonical_array_target() {
        let source = concat!(
            "interface Array<T> {}\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface IntrinsicElements { div: any; span: any; }\n",
            "}\n",
            "const view = <div><span>first</span>second</div>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_133);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/automatic-multiple-children.tsx\""),
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

        context
            .check_source_file_with_jsx_runtime(
                file,
                CanonicalJsxRuntimeEvidence::Automatic {
                    module_specifier: "/jsx/jsx-runtime",
                    resolved_module: Some(module),
                },
            )
            .unwrap();

        assert!(context.diagnostics().is_empty());
        let expression = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "view").then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.initializer?,
                ))
            })
            .unwrap();
        let NodeData::JsxElement(outer) = &parsed.arena.get(expression.node).unwrap().data else {
            unreachable!("the view initializer is the outer div")
        };
        let opening = child_ref(expression, outer.opening_element);
        let NodeData::JsxOpeningElement(opening_data) =
            &parsed.arena.get(opening.node).unwrap().data
        else {
            unreachable!("the outer div has an opening element")
        };
        let attributes = child_ref(opening, opening_data.attributes);
        let attributes_type = context
            .store()
            .type_node_links(attributes)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let members = context
            .store()
            .type_payload(attributes_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| context.store().symbol_table(members))
            .unwrap();
        let children = members.get_source("children").unwrap();
        let children_type = context
            .store()
            .value_symbol_links(children)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let reference = context
            .store()
            .canonical_array_reference(context.global_types(), children_type)
            .unwrap()
            .unwrap();
        assert_eq!(reference.base_type, children_type);
        assert!(!reference.readonly);
        assert!(!reference.array_literal);

        let super::super::TypeData::Union(union) = context
            .store()
            .type_payload(reference.element_type)
            .unwrap()
            .data()
        else {
            panic!("mixed JSX element and text children need a union element type")
        };
        let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
        let element_type = context
            .store()
            .type_node_links(expression)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&string_type));
        assert!(union.union.types.contains(&element_type));

        let nested = child_ref(expression, outer.children.nodes[0]);
        assert_eq!(
            context
                .store()
                .type_node_links(nested)
                .and_then(|links| links.resolved_type),
            Some(element_type),
        );
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
    fn automatic_runtime_multiple_children_use_the_missing_array_library_fallback() {
        let mut fixture = RuntimeFixture::new(
            "const view = <div>before<span />after</div>;\n",
            FileId::new(8_134),
        );
        let expression = fixture.expression("view");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        fixture.check(expression, CanonicalJsxRuntime::Automatic, &mut diagnostics);

        let NodeData::JsxElement(element) =
            &fixture.parsed.arena.get(expression.node).unwrap().data
        else {
            unreachable!("the view initializer is the outer div")
        };
        let opening = child_ref(expression, element.opening_element);
        let NodeData::JsxOpeningElement(opening_data) =
            &fixture.parsed.arena.get(opening.node).unwrap().data
        else {
            unreachable!("the outer div has an opening element")
        };
        let attributes = child_ref(opening, opening_data.attributes);
        let attributes_type = fixture
            .store
            .type_node_links(attributes)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let members = fixture
            .store
            .type_payload(attributes_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| fixture.store.symbol_table(members))
            .unwrap();
        let children = members.get_source("children").unwrap();

        assert_eq!(
            fixture
                .store
                .value_symbol_links(children)
                .and_then(|links| links.resolved_type),
            Some(
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .empty_object_type,
            ),
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
