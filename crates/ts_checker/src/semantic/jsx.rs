//! Canonical checking for basic JSX elements.
//!
//! This module follows the pinned JSX checker for global `JSX` namespaces,
//! named, indexed, or string-union intrinsic tags, and fixed or inferred
//! function components. Inline object-literal and identifier spreads reuse
//! canonical object publication. Dotted component names retain authenticated
//! namespace exports. Other spreads, broader contextual child expressions,
//! and factory imports remain explicit capability boundaries.

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
    RelationUnavailable, ResolvedSignatureState, SignatureId, SignatureLinks, SourceCheckError,
    SourceCheckProvenanceError, SourceLiteralCacheError, SourceSyntaxRole, SymbolNodeLinks, TypeId,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::UnionReduction,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    formatter::{
        AssignabilityErrorDisplay, CanonicalTypeFormatFlags,
        get_type_names_for_assignability_error,
        get_type_names_for_assignability_error_with_host_and_flags,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
        type_to_string_with_host_and_flags, type_to_string_with_host_global_types_and_flags,
    },
    indexed_access_types::template_pattern_index_matches_name,
    instantiate::{InstantiationLimits, InstantiationSession},
    instantiated_members::{demand_instantiated_property_type, resolve_members_with_array_targets},
    mapped_types::MappedTypeModifiers,
    production::{CanonicalJsxRuntime, CanonicalJsxRuntimeEvidence},
    reference_types::{create_direct_generic_reference, validate_direct_generic_reference},
    signatures::{ElementFlags, SignatureFlags},
    source::merge_retry_diagnostic,
    source_calls::{resolve_jsx_generic_component_signature, resolve_jsx_spread_call_signature},
    spelling::get_spelling_suggestion,
    tuple_types::CanonicalTupleTypeRequest,
    type_nodes::CanonicalTypeQuery,
    type_records::LiteralValue,
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
        closing: Option<Box<JsxClosingPlan>>,
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
    Array {
        node: NodeRef,
        elements: Vec<Self>,
    },
    Property {
        node: NodeRef,
        receiver: Box<Self>,
        name_node: NodeRef,
        name: String,
    },
    Call {
        node: NodeRef,
        callee: Box<Self>,
        arguments: Vec<Self>,
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
                Some(Box::new(JsxClosingPlan {
                    node: closing_node,
                    tag: plan_jsx_tag(arena, bound, store, closing_node, closing_data.tag_name)?,
                }))
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
                || value.declarations().is_none_or(<[NodeRef]>::is_empty)
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
            return if matches!(
                expression_record.kind,
                SyntaxKind::Identifier
                    | SyntaxKind::PropertyAccessExpression
                    | SyntaxKind::CallExpression
            ) {
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
    let receiver = match &value {
        JsxScalarPlan::Identifier { .. } => &value,
        JsxScalarPlan::Property { receiver, .. }
        | JsxScalarPlan::Call {
            callee: receiver, ..
        } => receiver.as_ref(),
        _ => return Err(unsupported(node, SyntaxKind::JsxSpreadAttribute)),
    };
    let JsxScalarPlan::Identifier {
        node: identifier,
        name,
    } = receiver
    else {
        return Err(unsupported(node, SyntaxKind::JsxSpreadAttribute));
    };
    if resolve_scoped_jsx_value_symbol(store, arena, bound, *identifier, name).is_none() {
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
        NodeData::ArrayLiteralExpression(array)
            if record.kind == SyntaxKind::ArrayLiteralExpression
                && array.facts == 0
                && !array.elements.nodes.is_empty()
                && !array.elements.has_trailing_comma =>
        {
            let mut elements = Vec::with_capacity(array.elements.nodes.len());
            for element in &array.elements.nodes {
                let element = child_ref(node, *element);
                let planned = plan_scalar(arena, bound, store, node, element)?;
                if !matches!(
                    planned,
                    JsxScalarPlan::String { .. }
                        | JsxScalarPlan::Number { .. }
                        | JsxScalarPlan::Boolean { .. }
                        | JsxScalarPlan::Identifier { .. }
                ) {
                    return Err(unsupported(element, SyntaxKind::ArrayLiteralExpression));
                }
                elements.push(planned);
            }
            Ok(JsxScalarPlan::Array { node, elements })
        }
        NodeData::CallExpression(call)
            if record.kind == SyntaxKind::CallExpression
                && call.question_dot_token.is_none()
                && call.symbol.is_none()
                && call.facts == 0
                && call.type_arguments.is_none()
                && !call.arguments.has_trailing_comma =>
        {
            let syntax = super::source_calls::plan_direct_source_call_syntax(arena, store, node)?;
            if syntax.callee_form() != super::source_calls::SourceCallCalleeForm::Identifier {
                return Err(unsupported(node, record.kind));
            }
            let callee = plan_scalar(arena, bound, store, node, syntax.callee())?;
            if !matches!(callee, JsxScalarPlan::Identifier { .. }) {
                return Err(unsupported(node, record.kind));
            }
            let arguments = syntax
                .arguments()
                .iter()
                .map(|argument| plan_scalar(arena, bound, store, node, *argument))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(JsxScalarPlan::Call {
                node,
                callee: Box::new(callee),
                arguments,
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
    let (arena, bound) = host.source(location).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingNode(location),
    ))?;
    let intrinsic_names = jsx_plan_intrinsic_names(store, arena, bound, plan);
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
        let Some(links) = store.alias_symbol_links(symbol) else {
            if is_unchecked_global_jsx_namespace_alias(store, symbol) {
                return Err(unsupported(
                    location,
                    store
                        .source_node_kind(location)
                        .unwrap_or(SyntaxKind::Identifier),
                ));
            }
            return Err(SourceCheckError::Import(location));
        };
        if links == &super::AliasSymbolLinks::default()
            && is_unchecked_global_jsx_namespace_alias(store, symbol)
        {
            return Err(unsupported(
                location,
                store
                    .source_node_kind(location)
                    .unwrap_or(SyntaxKind::Identifier),
            ));
        }
        if links.type_only_declaration.is_some() || links.immediate_target.is_none() {
            return Err(SourceCheckError::Import(location));
        }
        symbol = links
            .alias_target
            .symbol()
            .ok_or(SourceCheckError::Import(location))?;
    }
}

fn is_unchecked_global_jsx_namespace_alias(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
) -> bool {
    let Some(record) = store.symbol(alias) else {
        return false;
    };
    let Some([declaration]) = record.declarations() else {
        return false;
    };
    let declaration = *declaration;
    let Some(super::store::SourceNodeParent::Parent(source)) =
        store.source_node_parent(declaration)
    else {
        return false;
    };
    let Some(module) = record.parent() else {
        return false;
    };
    let Some(module_record) = store.symbol(module) else {
        return false;
    };
    let Some(exports) = module_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return false;
    };
    let Some(assignment) = exports.get(InternalSymbolName::ExportEquals.as_ref()) else {
        return false;
    };
    let Some(assignment_record) = store.symbol(assignment) else {
        return false;
    };
    let Some([assignment_declaration]) = assignment_record.declarations() else {
        return false;
    };
    let assignment_declaration = *assignment_declaration;

    record.flags() == SymbolFlags::ALIAS
        && record.check_flags() == CheckFlags::NONE
        && record.value_declaration().is_none()
        && record.members().is_none()
        && record.exports().is_none()
        && record.export_symbol().is_none()
        && store.get_merged_symbol(alias) == Some(alias)
        && store.source_node_kind(declaration) == Some(SyntaxKind::NamespaceExportDeclaration)
        && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
        && store.source_node_parent(source) == Some(super::store::SourceNodeParent::Root)
        && module_record.flags() == SymbolFlags::VALUE_MODULE
        && module_record.check_flags() == CheckFlags::NONE
        && module_record.declarations() == Some(&[source])
        && module_record.value_declaration() == Some(source)
        && module_record.parent().is_none()
        && module_record.export_symbol().is_none()
        && store.get_merged_symbol(module) == Some(module)
        && assignment_record.flags() == SymbolFlags::ALIAS
        && assignment_record.check_flags() == CheckFlags::NONE
        && assignment_record.name() == InternalSymbolName::ExportEquals.as_ref()
        && assignment_record.value_declaration() == Some(assignment_declaration)
        && assignment_record.members().is_none()
        && assignment_record.exports().is_none()
        && assignment_record.parent() == Some(module)
        && assignment_record.export_symbol().is_none()
        && store.get_merged_symbol(assignment) == Some(assignment)
        && store.source_node_kind(assignment_declaration) == Some(SyntaxKind::ExportAssignment)
        && store.source_node_parent(assignment_declaration)
            == Some(super::store::SourceNodeParent::Parent(source))
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get(record.name()))
            == Some(alias)
}

fn jsx_plan_intrinsic_names(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    plan: &JsxElementPlan,
) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_jsx_plan_intrinsic_names(store, arena, bound, plan, &mut names);
    names
}

fn collect_jsx_plan_intrinsic_names(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    plan: &JsxElementPlan,
    names: &mut HashSet<String>,
) {
    match &plan.kind {
        JsxElementPlanKind::Element {
            tag,
            attributes,
            closing,
            ..
        } => {
            if tag.intrinsic {
                names.insert(tag.name.clone());
            } else if let Some(symbol) = resolve_source_value_symbol(store, bound, &tag.name)
                && let Ok(type_) = jsx_component_value_type(store, arena, bound, symbol, tag.node)
                && let Some(intrinsics) = jsx_intrinsic_component_names(store, type_)
            {
                names.extend(intrinsics);
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
                            collect_jsx_scalar_intrinsic_names(store, arena, bound, value, names);
                        }
                    }
                }
                JsxAttributesPlan::ObjectSpread(spread) => {
                    for property in &spread.properties {
                        if let JsxAttributeValue::Expression { value, .. } = &property.value {
                            collect_jsx_scalar_intrinsic_names(store, arena, bound, value, names);
                        }
                    }
                }
                JsxAttributesPlan::SourceSpread(spread) => {
                    collect_jsx_scalar_intrinsic_names(store, arena, bound, &spread.value, names);
                }
            }
        }
        JsxElementPlanKind::Fragment => {}
    }
    for child in &plan.children {
        match child {
            JsxChildPlan::Text { .. } => {}
            JsxChildPlan::Expression { value, .. } => {
                collect_jsx_scalar_intrinsic_names(store, arena, bound, value, names);
            }
            JsxChildPlan::Element(element) => {
                collect_jsx_plan_intrinsic_names(store, arena, bound, element, names);
            }
        }
    }
}

fn collect_jsx_scalar_intrinsic_names(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    scalar: &JsxScalarPlan,
    names: &mut HashSet<String>,
) {
    match scalar {
        JsxScalarPlan::Element(element) => {
            collect_jsx_plan_intrinsic_names(store, arena, bound, element, names);
        }
        JsxScalarPlan::Property { receiver, .. } => {
            collect_jsx_scalar_intrinsic_names(store, arena, bound, receiver, names);
        }
        JsxScalarPlan::Call {
            callee, arguments, ..
        } => {
            collect_jsx_scalar_intrinsic_names(store, arena, bound, callee, names);
            for argument in arguments {
                collect_jsx_scalar_intrinsic_names(store, arena, bound, argument, names);
            }
        }
        JsxScalarPlan::Array { elements, .. } => {
            for element in elements {
                collect_jsx_scalar_intrinsic_names(store, arena, bound, element, names);
            }
        }
        JsxScalarPlan::TypeAssertion { value, .. } | JsxScalarPlan::Parenthesized { value, .. } => {
            collect_jsx_scalar_intrinsic_names(store, arena, bound, value, names);
        }
        JsxScalarPlan::Conditional {
            condition,
            when_true,
            when_false,
            ..
        } => {
            collect_jsx_scalar_intrinsic_names(store, arena, bound, condition, names);
            collect_jsx_scalar_intrinsic_names(store, arena, bound, when_true, names);
            collect_jsx_scalar_intrinsic_names(store, arena, bound, when_false, names);
        }
        JsxScalarPlan::AdjacentElements { left, right, .. } => {
            collect_jsx_plan_intrinsic_names(store, arena, bound, left, names);
            collect_jsx_plan_intrinsic_names(store, arena, bound, right, names);
        }
        JsxScalarPlan::String { .. }
        | JsxScalarPlan::Number { .. }
        | JsxScalarPlan::Boolean { .. }
        | JsxScalarPlan::Null(_)
        | JsxScalarPlan::GlobalThis(_)
        | JsxScalarPlan::Identifier { .. } => {}
    }
}

fn jsx_intrinsic_component_names(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<String>> {
    let record = store.type_payload(type_)?;
    match record.data() {
        super::TypeData::Literal(literal) if record.flags().contains(TypeFlags::STRING_LITERAL) => {
            let LiteralValue::String(name) = &literal.value else {
                return None;
            };
            (!name.is_empty()).then(|| vec![name.clone()])
        }
        super::TypeData::Union(union) if record.flags().contains(TypeFlags::UNION) => {
            let mut names = Vec::with_capacity(union.union.types.len());
            for constituent in &union.union.types {
                let record = store.type_payload(*constituent)?;
                let super::TypeData::Literal(literal) = record.data() else {
                    return None;
                };
                let LiteralValue::String(name) = &literal.value else {
                    return None;
                };
                if !record.flags().contains(TypeFlags::STRING_LITERAL) || name.is_empty() {
                    return None;
                }
                names.push(name.clone());
            }
            (!names.is_empty()).then_some(names)
        }
        _ => None,
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
                    for argument in type_arguments {
                        check_intrinsic_type_argument(
                            store,
                            host,
                            source.3,
                            plan.opening,
                            *argument,
                            options,
                            diagnostics,
                        )?;
                    }
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
                source.3,
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

    // Upstream checkJsxFragment recovers error types without changing nested elements.
    let element_type = if matches!(&plan.kind, JsxElementPlanKind::Fragment)
        && (namespace.element_type == namespace.error_type
            || store
                .type_payload(namespace.element_type)
                .is_some_and(|record| {
                    record.flags().intersects(TypeFlags::ANY) && record.alias().is_some()
                })) {
        namespace.any_type
    } else {
        namespace.element_type
    };
    publish_type_links(store, plan.expression, element_type)?;
    Ok(element_type)
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
        StoredCallableSetValidation::NotCallable => authenticated_fragment_component_attributes(
            store,
            host,
            fragment,
            plan.opening,
            options,
            diagnostics,
        )?,
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
        source.3,
        attributes,
        &property_name,
        plan.opening,
        options,
        diagnostics,
    )?
    else {
        return Ok(true);
    };
    if children.individual_errors
        || jsx_child_is_assignable(
            store,
            children.type_,
            expected,
            children.node,
            (host, source.3),
            options,
            diagnostics,
        )?
    {
        return Ok(true);
    }

    let actual = format_attribute_object(store, host, source.3, &[], Some(children))?;
    let expected_object = jsx_fragment_attributes_display(store, host, attributes, expected)?;
    let display = jsx_child_assignability_display(store, host, source.3, children.type_, expected)?;
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

#[allow(clippy::too_many_arguments)] // React child aliases retain authenticated global array types.
fn resolve_expected_jsx_child_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
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
    if let Some(property) = jsx_expected_attribute_property(store, expected, name, location)?
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
    let mut query = if let Some(global_types) = global_types {
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
    } else {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
    };
    query
        .get_declared_type_of_symbol(react_node)
        .map(Some)
        .map_err(Into::into)
}

fn contextual_jsx_child_element_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    expected: TypeId,
    index: usize,
) -> Result<TypeId, SourceCheckError> {
    let Some(global_types) = global_types else {
        return Ok(expected);
    };
    if let Some(array) = store.canonical_array_reference(global_types, expected)? {
        return Ok(array.element_type);
    }
    if let Some(tuple) = store
        .canonical_tuple_shape(expected)
        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(expected))?
    {
        let element = tuple.element_types().get(index).copied().or_else(|| {
            tuple
                .element_infos()
                .last()
                .filter(|info| info.flags().contains(ElementFlags::REST))
                .and_then(|_| tuple.element_types().last().copied())
        });
        return Ok(element.unwrap_or(expected));
    }

    let Some(super::TypeData::Union(union)) = store
        .type_payload(expected)
        .map(super::type_records::TypeRecord::data)
    else {
        return Ok(expected);
    };
    let constituents = union.union.types.clone();
    let mut projected = Vec::with_capacity(constituents.len());
    let mut has_sequence = false;
    for constituent in constituents {
        if let Some(array) = store.canonical_array_reference(global_types, constituent)? {
            projected.push(array.element_type);
            has_sequence = true;
        } else if let Some(tuple) = store
            .canonical_tuple_shape(constituent)
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(constituent))?
        {
            has_sequence = true;
            if let Some(element) = tuple.element_types().get(index).copied().or_else(|| {
                tuple
                    .element_infos()
                    .last()
                    .filter(|info| info.flags().contains(ElementFlags::REST))
                    .and_then(|_| tuple.element_types().last().copied())
            }) {
                projected.push(element);
            }
        } else {
            projected.push(constituent);
        }
    }
    if !has_sequence || projected.is_empty() {
        return Ok(expected);
    }

    store.validate_union_constituent_with_global_types(global_types, expected)?;
    store
        .expression_union_type_with_global_types(global_types, &projected, UnionReduction::None)
        .map_err(Into::into)
}

fn jsx_children_have_contextual_tuple(
    store: &CanonicalTypeMapperStore,
    expected: TypeId,
    length: usize,
) -> Result<bool, SourceCheckError> {
    let candidates = match store
        .type_payload(expected)
        .map(super::type_records::TypeRecord::data)
    {
        Some(super::TypeData::Union(union)) => union.union.types.as_slice(),
        Some(_) => std::slice::from_ref(&expected),
        None => return Err(RelationUnavailable::Type(expected).into()),
    };
    for candidate in candidates {
        if let Some(tuple) = store
            .canonical_tuple_shape(*candidate)
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(*candidate))?
            && !tuple.combined_flags().intersects(ElementFlags::VARIABLE)
            && tuple.min_length() <= length
            && length <= tuple.fixed_length()
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn contextual_jsx_children_tuple_type(
    store: &mut CanonicalTypeMapperStore,
    children: &[TypeId],
    expected: TypeId,
    location: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let required = store
        .create_tuple_element_info(ElementFlags::REQUIRED, None)
        .ok_or(SourceCheckError::Property(location))?;
    let infos = vec![required; children.len()];
    store
        .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(children, &infos, false))
        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(expected).into())
}

fn jsx_child_is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    location: NodeRef,
    (host, global_types): (&DeclaredTypeHost<'_>, Option<&CanonicalGlobalTypes>),
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<bool, SourceCheckError> {
    let (any, unknown) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        (bootstrap.any_type, bootstrap.unknown_type)
    };
    if source == unknown {
        let record = store
            .type_payload(source)
            .ok_or(SourceCheckError::Property(location))?;
        if record.flags() != TypeFlags::UNKNOWN
            || !matches!(
                record.data(),
                super::TypeData::Intrinsic(intrinsic) if intrinsic.intrinsic_name == "unknown"
            )
        {
            return Err(SourceCheckError::Property(location));
        }

        return Ok(target == any || target == unknown);
    }

    let relation = |store: &mut CanonicalTypeMapperStore, source| {
        if let Some(global_types) = global_types {
            store.is_type_assignable_to_with_global_types_and_strict_function_types(
                source,
                target,
                global_types,
                options.strict_function_types,
            )
        } else {
            store.is_type_assignable_to(source, target)
        }
    };
    let error = match relation(store, source) {
        Ok(assignable) => return Ok(assignable),
        Err(error @ RelationUnavailable::UnresolvedStructuredMembers(unresolved))
            if unresolved == source =>
        {
            error
        }
        Err(error @ RelationUnavailable::InvalidStructuredMembers(invalid))
            if matches!(
                store.type_payload(target).map(super::type_records::TypeRecord::data),
                Some(super::TypeData::Union(union)) if union.union.types.contains(&invalid)
            ) =>
        {
            error
        }
        Err(error) => return Err(error.into()),
    };

    let Some(owner) = store
        .type_payload(source)
        .and_then(super::type_records::TypeRecord::symbol)
    else {
        return Err(error.into());
    };
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return Err(error.into());
    };
    if store
        .symbol(owner)
        .and_then(|record| record.name().as_utf8())
        != Some("Element")
        || store
            .symbol(namespace)
            .and_then(|record| record.name().as_utf8())
            != Some("JSX")
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(source)
        || !jsx_namespace_interface_has_heritage(store, host, namespace, owner)?
    {
        return Err(error.into());
    }

    // Generic bases keep their arguments without resolving the JSX interface shell.
    let plan = super::object_members::plan_interface(store, host, owner)
        .ok()
        .filter(|plan| {
            plan.heritage.as_ref().is_none_or(|heritage| {
                heritage
                    .bases
                    .iter()
                    .all(|base| base.type_arguments.is_empty())
            })
        });
    let Some(plan) = plan else {
        let base = resolve_generic_jsx_element_base(
            store,
            host,
            owner,
            location,
            global_types,
            options,
            diagnostics,
        )?;
        if matches!(
            error,
            RelationUnavailable::InvalidStructuredMembers(invalid) if invalid != base
        ) {
            return Err(error.into());
        }
        if base == target {
            return Ok(true);
        }
        let includes_base = matches!(
            store.type_payload(target).map(super::type_records::TypeRecord::data),
            Some(super::TypeData::Union(union)) if union.union.types.contains(&base)
        );
        if includes_base {
            if let Some(global_types) = global_types {
                store.validate_union_constituent_with_global_types(global_types, target)?;
            } else {
                store.validate_union_constituent(target)?;
            }
            return Ok(true);
        }
        return relation(store, base).map_err(Into::into);
    };
    let mut bases = plan.heritage_base_symbols();
    let Some(base) = bases.next() else {
        return Err(error.into());
    };
    if bases.next().is_some() || !plan.properties.is_empty() {
        return Err(error.into());
    }
    let base_type = if let Some(global_types) = global_types {
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
            .get_declared_type_of_symbol(base)?
    } else {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
            .get_declared_type_of_symbol(base)?
    };
    let resolved = super::structured_members::resolve_direct_interface_members(
        store,
        &plan,
        source,
        &[],
        &[base_type],
    )
    .map_err(|_| SourceCheckError::Property(location))?;
    if resolved != source {
        return Err(SourceCheckError::Property(location));
    }

    relation(store, source).map_err(Into::into)
}

fn resolve_generic_jsx_element_base(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    location: NodeRef,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let invalid = || SourceCheckError::Property(location);
    let record = store.symbol(owner).ok_or_else(invalid)?;
    let Some([declaration]) = record.declarations() else {
        return Err(invalid());
    };
    let declaration = *declaration;
    let declaration_record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &declaration_record.data else {
        return Err(invalid());
    };
    let Some(clauses) = interface.heritage_clauses.as_ref() else {
        return Err(invalid());
    };
    if declaration_record.kind != SyntaxKind::InterfaceDeclaration
        || declaration_record.flags.0 != 0
        || !host.symbol_matches(store, declaration, owner)
        || interface.type_parameters.is_some()
        || !interface.members.nodes.is_empty()
    {
        return Err(invalid());
    }

    let heritage = super::interface_heritage::plan_direct_interface_heritage(
        store,
        host,
        declaration,
        owner,
        clauses,
    )
    .map_err(|_| invalid())?;
    let [base] = heritage.bases.as_slice() else {
        return Err(invalid());
    };
    if base.type_arguments.is_empty()
        || base.kind != super::interface_heritage::DirectInterfaceBaseKind::Interface
    {
        return Err(invalid());
    }

    let mut query = if let Some(global_types) = global_types {
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
    } else {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
    };
    let target = query.get_declared_type_of_symbol(base.symbol)?;
    let mut arguments = Vec::with_capacity(base.type_arguments.len());
    for argument in &base.type_arguments {
        arguments.push(query.get_type_from_type_node(*argument)?);
    }
    create_direct_generic_reference(store, target, &arguments, ObjectFlags::NONE)
        .map_err(|_| invalid())
}

fn jsx_child_assignability_display(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    mut source: TypeId,
    target: TypeId,
) -> Result<AssignabilityErrorDisplay, SourceCheckError> {
    if let Some(record) = store.type_payload(source)
        && record.flags().intersects(TypeFlags::STRING_LITERAL)
        && matches!(
            record.data(),
            super::TypeData::Literal(literal)
                if literal.fresh_type == Some(source) && literal.regular_type != source
        )
        && let Some(super::TypeData::Union(union)) = store
            .type_payload(target)
            .map(super::type_records::TypeRecord::data)
        && union.union.types.iter().all(|constituent| {
            store
                .type_payload(*constituent)
                .is_some_and(|record| !record.flags().intersects(TypeFlags::STRING_LITERAL))
        })
    {
        store.validate_union_constituent(source)?;
        source = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?
            .string_type;
    }
    let mut display = if let Some(global_types) = global_types {
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            source,
            target,
            CanonicalTypeFormatFlags::NONE,
        )
    } else {
        get_type_names_for_assignability_error_with_host_and_flags(
            store,
            host,
            source,
            target,
            CanonicalTypeFormatFlags::NONE,
        )
    }
    .map_err(SourceCheckError::from)?;
    if display.target == "React.ReactNode"
        && contextual_react_node_alias(store, host, target).is_some()
    {
        "ReactNode".clone_into(&mut display.target);
    }
    Ok(display)
}

fn jsx_fragment_attributes_display(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    attributes: TypeId,
    child: TypeId,
) -> Result<String, SourceCheckError> {
    if let Some(alias) = contextual_react_node_alias(store, host, child)
        && let Some(structured) = store
            .type_payload(attributes)
            .and_then(|record| record.data().structured())
        && let Some([property]) = structured.properties.as_deref()
        && let Some(record) = store.symbol(*property)
        && record
            .flags()
            .contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
        && record.check_flags() == CheckFlags::NONE
        && record.name().as_utf8() == Some("children")
        && structured
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("children"))
            == Some(*property)
        && store
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
            == Some(child)
    {
        return Ok(format!("{{ children?: {alias}; }}"));
    }

    type_to_string_with_host_and_flags(
        store,
        host,
        attributes,
        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
    )
    .map_err(Into::into)
}

fn contextual_react_node_alias(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
) -> Option<&'static str> {
    let record = store.type_payload(type_)?;
    if !matches!(record.data(), super::TypeData::Union(_)) {
        return None;
    }
    let alias = store.type_alias(record.alias()?)?;
    if alias.type_arguments().is_some() {
        return None;
    }
    let symbol = alias.symbol()?;
    let owner = store.symbol(symbol)?;
    let [declaration] = owner.declarations()? else {
        return None;
    };
    let declaration = *declaration;
    let namespace = store.get_parent_of_symbol(symbol)?;
    let namespace_record = store.symbol(namespace)?;
    let globals = store.intrinsic_bootstrap()?.globals;
    if owner.flags() != SymbolFlags::TYPE_ALIAS
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("ReactNode")
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.type_alias_links(symbol).is_none_or(|links| {
            links.declared_type != Some(type_) || links.type_parameters.is_some()
        })
        || host.node(declaration).is_none_or(|node| {
            node.kind != SyntaxKind::TypeAliasDeclaration
                || !matches!(node.data, NodeData::TypeAliasDeclaration(_))
        })
        || !host.symbol_matches(store, declaration, symbol)
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("React")
        || store.get_merged_symbol(namespace) != Some(namespace)
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("ReactNode"))
            .and_then(|export| store.get_merged_symbol(export))
            != Some(symbol)
        || store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .and_then(|global| store.get_merged_symbol(global))
            != Some(namespace)
    {
        return None;
    }

    Some("ReactNode")
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
    let expected_children = if plan.children.len() > 1 {
        resolve_expected_jsx_child_type(
            store,
            source.2,
            source.3,
            expected_attributes,
            &property_name,
            plan.opening,
            options,
            diagnostics,
        )?
    } else {
        None
    };
    let constructor_overload = if expected_children.is_some() {
        jsx_constructor_overload_declaration(store, source.2, plan)?
    } else {
        None
    };
    let mut individual_errors = false;
    for (index, child) in plan.children.iter().enumerate() {
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
        if let Some(expected) = expected_children
            .map(|expected| contextual_jsx_child_element_type(store, source.3, expected, index))
            .transpose()?
            && !jsx_child_is_assignable(
                store,
                type_,
                expected,
                node,
                (source.2, source.3),
                options,
                diagnostics,
            )?
        {
            let display =
                jsx_child_assignability_display(store, source.2, source.3, type_, expected)?;
            if let Some(declaration) = constructor_overload {
                add_jsx_constructor_overload_child_diagnostic(
                    diagnostics,
                    node,
                    declaration,
                    display,
                )?;
            } else {
                add_diagnostic(diagnostics, node, 2322, [display.source, display.target])?;
            }
            individual_errors = true;
        }
        child_types.push(type_);
    }

    let node = first_node.expect("a nonempty JSX child plan has a first child");
    let type_ = if let [type_] = child_types.as_slice() {
        *type_
    } else if let Some(expected) = expected_children
        && jsx_children_have_contextual_tuple(store, expected, child_types.len())?
    {
        contextual_jsx_children_tuple_type(store, &child_types, expected, node)?
    } else {
        let element = if let Some(global_types) = source.3 {
            let mut prepared = store.prepare_type_query_types_with_global_types(
                &[],
                &[],
                &[],
                1,
                0,
                global_types,
            )?;
            store.literal_union_type_prepared_with_global_types(
                global_types,
                &child_types,
                None,
                &mut prepared,
            )?
        } else {
            let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
            store.literal_union_type_prepared(&child_types, None, &mut prepared)?
        };
        automatic_jsx_children_array_type(store, source.2, element, node)?
    };
    Ok(Some(CheckedJsxChildren {
        node,
        type_,
        name,
        individual_errors,
    }))
}

fn jsx_constructor_overload_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &JsxElementPlan,
) -> Result<Option<NodeRef>, SourceCheckError> {
    let JsxElementPlanKind::Element { tag, .. } = &plan.kind else {
        return Ok(None);
    };
    if tag.intrinsic {
        return Ok(None);
    }
    let component = store
        .type_node_links(tag.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.opening))?;
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, component)
    else {
        return Ok(None);
    };
    if !projection.call_signatures.is_empty() || projection.construct_signatures.len() < 2 {
        return Ok(None);
    }
    let signature = *projection
        .construct_signatures
        .last()
        .ok_or(SourceCheckError::Call(plan.opening))?;
    if store
        .signature_links(plan.opening)
        .and_then(|links| links.resolved_signature.signature())
        != Some(signature)
    {
        return Err(SourceCheckError::Call(plan.opening));
    }
    let declaration = store
        .signature(signature)
        .and_then(super::signatures::Signature::declaration)
        .ok_or(SourceCheckError::Call(plan.opening))?;
    if host.node(declaration).is_none_or(|record| {
        !matches!(
            record.kind,
            SyntaxKind::Constructor | SyntaxKind::ConstructSignature
        )
    }) {
        return Err(SourceCheckError::Call(plan.opening));
    }
    Ok(Some(declaration))
}

fn add_jsx_constructor_overload_child_diagnostic(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    declaration: NodeRef,
    display: AssignabilityErrorDisplay,
) -> Result<(), SourceCheckError> {
    let overload =
        Diagnostic::new(message_by_code(2770).ok_or(SourceCheckError::MissingDiagnostic(2770))?)
            .render()
            .map_err(|_| SourceCheckError::MissingDiagnostic(2770))?;
    let child = Diagnostic::with_arguments(
        message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
        [display.source, display.target],
    )
    .render()
    .map_err(|_| SourceCheckError::MissingDiagnostic(2322))?;
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2769).ok_or(SourceCheckError::MissingDiagnostic(2769))?,
            )
            .with_details([format!("  {overload}"), format!("    {child}")]),
            related_information: vec![CanonicalCheckerRelatedInformation {
                node: Some(declaration),
                diagnostic: Diagnostic::new(
                    message_by_code(2771).ok_or(SourceCheckError::MissingDiagnostic(2771))?,
                ),
            }],
        },
    );
    Ok(())
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
    let mut overlapping_patterns = false;
    let mut string_index = None;
    for &index in &indexes {
        let info = store
            .index_info(index)
            .ok_or(SourceCheckError::Property(opening))?;
        if info.key_type() == string_type {
            string_index.get_or_insert(index);
        } else if template_pattern_index_matches_name(store, info.key_type(), &tag.name) {
            overlapping_patterns |= patterned_index.replace(index).is_some();
        }
    }

    if overlapping_patterns {
        return resolve_overlapping_intrinsic_indexes(
            store,
            bound,
            opening,
            tag,
            owner,
            &indexes,
            string_type,
        );
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

/// Combines matching template indexes without changing their individual cache entries.
#[allow(clippy::too_many_lines)] // Matching values and every contributing declaration share one proof.
fn resolve_overlapping_intrinsic_indexes(
    store: &mut CanonicalTypeMapperStore,
    bound: &BoundFile,
    opening: NodeRef,
    tag: &JsxTagPlan,
    owner: Option<SemanticSymbolId>,
    indexes: &[super::IndexInfoId],
    string_type: TypeId,
) -> Result<JsxIntrinsicResolution, SourceCheckError> {
    if indexes.len() < 2 {
        return Err(SourceCheckError::Property(opening));
    }
    if let Some(symbol) = store
        .symbol_node_links(tag.node)
        .and_then(|links| links.resolved_symbol)
        && store
            .symbol(symbol)
            .is_none_or(|record| record.check_flags() != CheckFlags::INDEX_SYMBOL)
    {
        return Err(unsupported(opening, SyntaxKind::IndexSignature));
    }

    let mut declarations = Vec::with_capacity(indexes.len());
    let mut value_types = Vec::with_capacity(indexes.len());
    for index in indexes {
        let info = store
            .index_info(*index)
            .ok_or(SourceCheckError::Property(opening))?;
        let patterned = info.key_type() != string_type
            && template_pattern_index_matches_name(store, info.key_type(), &tag.name);
        if info.key_type() != string_type && !patterned {
            continue;
        }
        let declaration = info
            .declaration()
            .ok_or_else(|| unsupported(opening, SyntaxKind::IndexSignature))?;
        if !bound.contains(declaration)
            && !authenticated_foreign_intrinsic_index_declaration(store, owner, declaration)
            || declarations.contains(&declaration)
        {
            return Err(SourceCheckError::Property(opening));
        }
        if let Some(symbol) = info.index_symbol() {
            validate_index_symbol(
                store,
                symbol,
                owner,
                Some(declaration),
                info.value_type(),
                opening,
            )?;
        }
        declarations.push(declaration);
        if patterned {
            value_types.push(info.value_type());
        }
    }
    if value_types.len() < 2 {
        return Err(SourceCheckError::Property(opening));
    }

    let attributes_type = store
        .canonical_intersection_type(&value_types, None)
        .map_err(|_| unsupported(opening, SyntaxKind::IndexSignature))?;
    let declaration = declarations[0];
    if let Some(symbol) = store
        .symbol_node_links(opening)
        .and_then(|links| links.resolved_symbol)
    {
        validate_index_symbol(
            store,
            symbol,
            owner,
            Some(declaration),
            attributes_type,
            opening,
        )?;
        if store
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::declarations)
            != Some(declarations.as_slice())
        {
            return Err(SourceCheckError::Property(opening));
        }
        return Ok(JsxIntrinsicResolution {
            symbol,
            attributes_type,
            flags: JsxFlags::INTRINSIC_INDEXED_ELEMENT,
        });
    }

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
            declarations: Some(declarations),
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
            resolved_type: Some(attributes_type),
            ..ValueSymbolLinks::default()
        },
    ) {
        return Err(SourceCheckError::Property(opening));
    }
    Ok(JsxIntrinsicResolution {
        symbol,
        attributes_type,
        flags: JsxFlags::INTRINSIC_INDEXED_ELEMENT,
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
    if let Some(names) = jsx_intrinsic_component_names(store, component) {
        return resolve_intrinsic_component_tag(
            store,
            bound,
            namespace,
            opening,
            tag,
            &names,
            options,
            diagnostics,
        );
    }

    let callable = match validate_stored_callable_set(store, component) {
        StoredCallableSetValidation::Valid { projection, .. }
            if projection.construct_signatures.is_empty()
                && projection.call_signatures.len() == 1 =>
        {
            projection.call_signatures[0].clone()
        }
        StoredCallableSetValidation::Valid { projection, .. }
            if projection.call_signatures.is_empty()
                && !projection.construct_signatures.is_empty() =>
        {
            let overload_count = projection.construct_signatures.len();
            let signature = *projection
                .construct_signatures
                .last()
                .ok_or(SourceCheckError::Call(opening))?;
            return resolve_construct_component_signature(
                store,
                host,
                namespace,
                opening,
                (signature, overload_count),
                options,
                diagnostics,
            );
        }
        StoredCallableSetValidation::NotCallable
            if tag.namespace_member.is_some()
                && store
                    .symbol(symbol)
                    .and_then(|record| record.name().as_utf8())
                    == Some("Fragment") =>
        {
            let attributes = authenticated_fragment_component_attributes(
                store,
                host,
                symbol,
                tag.node,
                options,
                diagnostics,
            )?;
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

fn resolve_construct_component_signature(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: &JsxNamespace,
    opening: NodeRef,
    constructor: (SignatureId, usize),
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(TypeId, SignatureId), SourceCheckError> {
    let invalid = || SourceCheckError::Call(opening);
    let (signature, overload_count) = constructor;
    let record = store.signature(signature).ok_or_else(invalid)?;
    let (parameter, remaining) = match record.parameters().split_first() {
        Some((parameter, remaining)) => (Some(*parameter), remaining),
        None => (None, &[][..]),
    };
    if overload_count == 0
        || overload_count == 1 && !remaining.is_empty()
        || overload_count > 1 && (parameter.is_none() || remaining.len() > 1)
    {
        return Err(unsupported(opening, SyntaxKind::JsxOpeningElement));
    }
    let attributes = parameter
        .map(|parameter| {
            store
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type)
                .filter(|type_| store.type_payload(*type_).is_some())
                .ok_or_else(invalid)
        })
        .transpose()?;
    let result = record.resolved_return_type().ok_or_else(invalid)?;
    let parameter_types = store
        .callable_signature_parameter_types(signature)
        .ok_or_else(invalid)?;
    let allowed = SignatureFlags::CONSTRUCT | SignatureFlags::HAS_LITERAL_TYPES;
    if !record.flags().contains(SignatureFlags::CONSTRUCT)
        || record.flags().bits() & !allowed.bits() != 0
        || record.this_parameter().is_some()
        || !record.type_parameters().is_empty()
        || record.min_argument_count() < 0
        || usize::try_from(record.min_argument_count())
            .ok()
            .is_none_or(|minimum| minimum > record.parameters().len())
        || parameter_types.len() != record.parameters().len()
        || parameter_types.first().copied() != attributes
        || record
            .parameters()
            .iter()
            .zip(parameter_types)
            .any(|(parameter, type_)| {
                store
                    .value_symbol_links(*parameter)
                    .and_then(|links| links.resolved_type)
                    != Some(*type_)
            })
        || store.type_payload(result).is_none()
    {
        return Err(invalid());
    }

    if let Some(name) = resolve_construct_component_attributes_property(
        store,
        host,
        namespace,
        opening,
        options,
        diagnostics,
    )? {
        if let Some(property) = store.resolved_own_property(result, &name)? {
            return Ok((property.type_, signature));
        }
        add_diagnostic(diagnostics, opening, 2607, [name])?;
        return Ok((namespace.error_type, signature));
    }

    let attributes = attributes.unwrap_or_else(|| {
        store
            .intrinsic_bootstrap()
            .expect("the checker bootstrap was validated")
            .empty_object_type
    });
    Ok((attributes, signature))
}

fn resolve_construct_component_attributes_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: &JsxNamespace,
    opening: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<Option<String>, SourceCheckError> {
    let Some(element) = store
        .type_payload(namespace.element_type)
        .and_then(super::type_records::TypeRecord::symbol)
    else {
        return Ok(None);
    };
    let Some(owner) = store.get_parent_of_symbol(element) else {
        return Ok(None);
    };
    let Some(marker) = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("ElementAttributesProperty"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    validate_jsx_namespace_type_symbol(store, marker, opening)?;
    let marker_type =
        resolve_namespace_export_type(store, host, owner, marker, None, options, diagnostics)?;
    let properties = store
        .type_payload(marker_type)
        .and_then(|record| record.data().structured())
        .ok_or(SourceCheckError::Property(opening))?
        .properties
        .as_deref()
        .unwrap_or_default();
    match properties {
        [] => Ok(None),
        [property] => {
            let record = store
                .symbol(*property)
                .ok_or(SourceCheckError::Property(opening))?;
            if !record.flags().contains(SymbolFlags::PROPERTY)
                || record.name().as_utf8().is_none_or(str::is_empty)
            {
                return Err(SourceCheckError::Property(opening));
            }
            Ok(record.name().as_utf8().map(str::to_owned))
        }
        _ => {
            let declaration = store
                .symbol(marker)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first().copied())
                .ok_or(SourceCheckError::Property(opening))?;
            add_diagnostic(
                diagnostics,
                declaration,
                2608,
                ["ElementAttributesProperty"],
            )?;
            Ok(None)
        }
    }
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

    let is_fragment = record.name().as_utf8() == Some("Fragment");
    let legacy_component = if let NodeData::TypeReferenceNode(reference) = &annotation_record.data
        && is_fragment
    {
        let name = child_ref(annotation, reference.type_name);
        host.node(name).is_some_and(|record| {
            matches!(
                &record.data,
                NodeData::Identifier(identifier) if identifier.text == "ComponentType"
            )
        })
    } else {
        false
    };
    let type_ = if legacy_component {
        resolve_legacy_react_fragment_component(
            store,
            host,
            member,
            annotation,
            options,
            diagnostics,
        )?
    } else if let NodeData::TypeReferenceNode(reference) = &annotation_record.data
        && is_fragment
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

#[allow(clippy::too_many_lines)] // The legacy alias and both component owners require one proof.
fn validate_legacy_react_fragment_component_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: SemanticSymbolId,
    annotation: NodeRef,
    name: NodeRef,
) -> Result<(), SourceCheckError> {
    let namespace_record = store
        .symbol(namespace)
        .ok_or(SourceCheckError::Property(annotation))?;
    let exports = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Property(annotation))?;
    let alias = exports
        .get_source("ComponentType")
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Property(annotation))?;
    let alias_record = store
        .symbol(alias)
        .ok_or(SourceCheckError::Property(annotation))?;
    let [declaration] = alias_record
        .declarations()
        .ok_or(SourceCheckError::Property(annotation))?
    else {
        return Err(SourceCheckError::Property(annotation));
    };
    let declaration = *declaration;
    let declaration_record = host
        .node(declaration)
        .ok_or(SourceCheckError::Property(annotation))?;
    let NodeData::TypeAliasDeclaration(alias_data) = &declaration_record.data else {
        return Err(SourceCheckError::Property(annotation));
    };
    let parameters = alias_data
        .type_parameters
        .as_ref()
        .ok_or(SourceCheckError::Property(annotation))?;
    let [parameter] = parameters.nodes.as_slice() else {
        return Err(SourceCheckError::Property(annotation));
    };
    let parameter = child_ref(declaration, *parameter);
    let parameter_record = host
        .node(parameter)
        .ok_or(SourceCheckError::Property(annotation))?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(SourceCheckError::Property(annotation));
    };
    let parameter_name = child_ref(parameter, parameter_data.name);
    let parameter_name_record = host
        .node(parameter_name)
        .ok_or(SourceCheckError::Property(annotation))?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(SourceCheckError::Property(annotation));
    };
    let default = parameter_data
        .default_type
        .map(|default| child_ref(parameter, default))
        .ok_or(SourceCheckError::Property(annotation))?;
    let default_record = host
        .node(default)
        .ok_or(SourceCheckError::Property(annotation))?;
    let NodeData::TypeLiteralNode(default_data) = &default_record.data else {
        return Err(SourceCheckError::Property(annotation));
    };
    let union = child_ref(declaration, alias_data.type_);
    let union_record = host
        .node(union)
        .ok_or(SourceCheckError::Property(annotation))?;
    let NodeData::UnionTypeNode(union_data) = &union_record.data else {
        return Err(SourceCheckError::Property(annotation));
    };
    let [class, function] = union_data.types.nodes.as_slice() else {
        return Err(SourceCheckError::Property(annotation));
    };
    let facts = host
        .bound_file(declaration)
        .and_then(ts_binder::BoundFile::source_facts)
        .ok_or(SourceCheckError::Property(annotation))?;
    if !facts.is_declaration_file()
        || facts.is_default_library()
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("React")
        || alias_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_ALIAS
        || alias_record.check_flags() != CheckFlags::NONE
        || alias_record.name().as_utf8() != Some("ComponentType")
        || store.get_parent_of_symbol(alias) != Some(namespace)
        || !host.symbol_matches(store, declaration, alias)
        || declaration_record.kind != SyntaxKind::TypeAliasDeclaration
        || declaration_record.flags.0 != 0
        || parameters.has_trailing_comma
        || parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.constraint.is_some()
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.flags.0 != 0
        || parameter_name_record.parent != Some(parameter.node)
        || parameter_identifier.flow_node.is_some()
        || parameter_identifier.text != "P"
        || default_record.kind != SyntaxKind::TypeLiteral
        || default_record.flags.0 != 0
        || default_record.parent != Some(parameter.node)
        || !default_data.members.nodes.is_empty()
        || union_record.kind != SyntaxKind::UnionType
        || union_record.flags.0 != 0
        || union_record.parent != Some(declaration.node)
        || union_data.types.has_trailing_comma
    {
        return Err(SourceCheckError::Property(annotation));
    }
    let mut resolver = host.name_resolver_host(store)?;
    if resolver
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(super::DeclaredTypeError::from)?
        .and_then(|resolved| store.get_merged_symbol(resolved))
        != Some(alias)
    {
        return Err(SourceCheckError::Property(annotation));
    }

    for (component, expected) in [
        (*class, "ComponentClass"),
        (*function, "StatelessComponent"),
    ] {
        let component = child_ref(union, component);
        let component_record = host
            .node(component)
            .ok_or(SourceCheckError::Property(annotation))?;
        let NodeData::TypeReferenceNode(reference) = &component_record.data else {
            return Err(SourceCheckError::Property(annotation));
        };
        let component_name = child_ref(component, reference.type_name);
        let component_name_record = host
            .node(component_name)
            .ok_or(SourceCheckError::Property(annotation))?;
        let NodeData::Identifier(identifier) = &component_name_record.data else {
            return Err(SourceCheckError::Property(annotation));
        };
        let arguments = reference
            .type_arguments
            .as_ref()
            .ok_or(SourceCheckError::Property(annotation))?;
        let [argument] = arguments.nodes.as_slice() else {
            return Err(SourceCheckError::Property(annotation));
        };
        let argument = child_ref(component, *argument);
        let argument_record = host
            .node(argument)
            .ok_or(SourceCheckError::Property(annotation))?;
        let NodeData::TypeReferenceNode(argument_reference) = &argument_record.data else {
            return Err(SourceCheckError::Property(annotation));
        };
        let argument_name = child_ref(argument, argument_reference.type_name);
        let argument_name_record = host
            .node(argument_name)
            .ok_or(SourceCheckError::Property(annotation))?;
        let NodeData::Identifier(argument_identifier) = &argument_name_record.data else {
            return Err(SourceCheckError::Property(annotation));
        };
        let symbol = exports
            .get_source(expected)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or(SourceCheckError::Property(annotation))?;
        let owner = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Property(annotation))?;
        if component_record.kind != SyntaxKind::TypeReference
            || component_record.flags.0 != 0
            || component_record.parent != Some(union.node)
            || arguments.has_trailing_comma
            || component_name_record.kind != SyntaxKind::Identifier
            || component_name_record.flags.0 != 0
            || component_name_record.parent != Some(component.node)
            || identifier.flow_node.is_some()
            || identifier.text != expected
            || argument_record.kind != SyntaxKind::TypeReference
            || argument_record.flags.0 != 0
            || argument_record.parent != Some(component.node)
            || argument_reference.type_arguments.is_some()
            || argument_name_record.kind != SyntaxKind::Identifier
            || argument_name_record.flags.0 != 0
            || argument_name_record.parent != Some(argument.node)
            || argument_identifier.flow_node.is_some()
            || argument_identifier.text != parameter_identifier.text
            || owner.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
            || owner.check_flags() != CheckFlags::NONE
            || owner.name().as_utf8() != Some(expected)
            || store.get_parent_of_symbol(symbol) != Some(namespace)
            || resolver
                .resolve_entity_name(component_name, SymbolFlags::TYPE)
                .map_err(super::DeclaredTypeError::from)?
                .and_then(|resolved| store.get_merged_symbol(resolved))
                != Some(symbol)
        {
            return Err(SourceCheckError::Property(annotation));
        }
    }
    Ok(())
}

/// Authenticates React 16's `ComponentType<P = {}>` and selects its real SFC branch.
#[allow(clippy::too_many_lines)] // Alias, defaults, namespace exports, and generic references share one proof.
fn resolve_legacy_react_fragment_component(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: &JsxNamespaceMemberPlan,
    annotation: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let invalid = || SourceCheckError::Property(annotation);
    let record = host.node(annotation).ok_or_else(invalid)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Err(invalid());
    };
    let name = child_ref(annotation, reference.type_name);
    validate_legacy_react_fragment_component_type(store, host, member.namespace, annotation, name)?;
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let namespace = store.symbol(member.namespace).ok_or_else(invalid)?;
    let exports = namespace
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(invalid)?;
    let alias = exports
        .get_source("ComponentType")
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let alias_record = store.symbol(alias).ok_or_else(invalid)?;
    let Some([declaration]) = alias_record.declarations() else {
        return Err(invalid());
    };
    let declaration = *declaration;
    let declaration_record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::TypeAliasDeclaration(alias_data) = &declaration_record.data else {
        return Err(invalid());
    };
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let parameters = alias_data.type_parameters.as_ref().ok_or_else(invalid)?;
    let [parameter_id] = parameters.nodes.as_slice() else {
        return Err(invalid());
    };
    let parameter = child_ref(declaration, *parameter_id);
    let parameter_record = host.node(parameter).ok_or_else(invalid)?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let parameter_name = child_ref(parameter, parameter_data.name);
    let parameter_name_record = host.node(parameter_name).ok_or_else(invalid)?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(invalid());
    };
    let default = parameter_data
        .default_type
        .map(|default| child_ref(parameter, default))
        .ok_or_else(invalid)?;
    let default_record = host.node(default).ok_or_else(invalid)?;
    let NodeData::TypeLiteralNode(default_literal) = &default_record.data else {
        return Err(invalid());
    };
    let body = child_ref(declaration, alias_data.type_);
    let body_record = host.node(body).ok_or_else(invalid)?;
    let NodeData::UnionTypeNode(union) = &body_record.data else {
        return Err(invalid());
    };
    let [class_id, stateless_id] = union.types.nodes.as_slice() else {
        return Err(invalid());
    };
    let parameter_symbol = bound
        .symbol(parameter)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    if record.kind != SyntaxKind::TypeReference
        || reference.type_arguments.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(annotation.node)
        || identifier.flow_node.is_some()
        || identifier.text != "ComponentType"
        || !namespace.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace.name().as_utf8() != Some("React")
        || !alias_record.flags().contains(SymbolFlags::TYPE_ALIAS)
        || alias_record.check_flags() != CheckFlags::NONE
        || alias_record.name().as_utf8() != Some("ComponentType")
        || store.get_parent_of_symbol(alias) != Some(member.namespace)
        || !host.symbol_matches(store, declaration, alias)
        || declaration_record.kind != SyntaxKind::TypeAliasDeclaration
        || declaration_record.flags.0 != 0
        || parameters.has_trailing_comma
        || parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.constraint.is_some()
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.parent != Some(parameter.node)
        || parameter_identifier.text != "P"
        || default_record.kind != SyntaxKind::TypeLiteral
        || default_record.parent != Some(parameter.node)
        || !default_literal.members.nodes.is_empty()
        || body_record.kind != SyntaxKind::UnionType
        || body_record.parent != Some(declaration.node)
        || union.types.has_trailing_comma
    {
        return Err(invalid());
    }

    let mut stateless = None;
    for (node, expected) in [
        (*class_id, "ComponentClass"),
        (*stateless_id, "StatelessComponent"),
    ] {
        let reference_node = child_ref(body, node);
        let reference_record = host.node(reference_node).ok_or_else(invalid)?;
        let NodeData::TypeReferenceNode(component) = &reference_record.data else {
            return Err(invalid());
        };
        let component_name = child_ref(reference_node, component.type_name);
        let component_name_record = host.node(component_name).ok_or_else(invalid)?;
        let NodeData::Identifier(component_identifier) = &component_name_record.data else {
            return Err(invalid());
        };
        let arguments = component.type_arguments.as_ref().ok_or_else(invalid)?;
        let [argument_id] = arguments.nodes.as_slice() else {
            return Err(invalid());
        };
        let argument = child_ref(reference_node, *argument_id);
        let argument_record = host.node(argument).ok_or_else(invalid)?;
        let NodeData::TypeReferenceNode(argument_reference) = &argument_record.data else {
            return Err(invalid());
        };
        let argument_name = child_ref(argument, argument_reference.type_name);
        let argument_name_record = host.node(argument_name).ok_or_else(invalid)?;
        let NodeData::Identifier(argument_identifier) = &argument_name_record.data else {
            return Err(invalid());
        };
        let symbol = exports
            .get_source(expected)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or_else(invalid)?;
        let owner = store.symbol(symbol).ok_or_else(invalid)?;
        if reference_record.kind != SyntaxKind::TypeReference
            || reference_record.parent != Some(body.node)
            || component_name_record.kind != SyntaxKind::Identifier
            || component_name_record.parent != Some(reference_node.node)
            || component_identifier.text != expected
            || arguments.has_trailing_comma
            || argument_record.kind != SyntaxKind::TypeReference
            || argument_record.parent != Some(reference_node.node)
            || argument_reference.type_arguments.is_some()
            || argument_name_record.kind != SyntaxKind::Identifier
            || argument_name_record.parent != Some(argument.node)
            || argument_identifier.text != "P"
            || bound
                .locals(declaration)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source("P"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(parameter_symbol)
            || !owner.flags().contains(SymbolFlags::INTERFACE)
            || owner.check_flags() != CheckFlags::NONE
            || owner.name().as_utf8() != Some(expected)
            || store.get_parent_of_symbol(symbol) != Some(member.namespace)
        {
            return Err(invalid());
        }
        if expected == "StatelessComponent" {
            stateless = Some(symbol);
        }
    }

    let props = CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_type_from_type_node(default)?;
    let target = store.get_declared_type_of_symbol(host, stateless.ok_or_else(invalid)?)?;
    create_direct_generic_reference(store, target, &[props], ObjectFlags::FROM_TYPE_NODE)
        .map_err(|_| invalid())
}

fn authenticated_fragment_component_attributes(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    location: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
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
    let target_name = store
        .symbol(target)
        .and_then(|record| record.name().as_utf8())
        .ok_or(SourceCheckError::Property(location))?;
    if !matches!(target_name, "ExoticComponent" | "StatelessComponent")
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
    if target_name == "StatelessComponent" {
        return legacy_react_fragment_attributes(
            store,
            host,
            symbol,
            target,
            location,
            options,
            diagnostics,
        );
    }
    Ok(*attributes)
}

/// Selects the authenticated `{ children?: ReactNode }` half of React 16 SFC props.
#[allow(clippy::too_many_lines)] // Signature, generic parameter, and children property form one proof.
fn legacy_react_fragment_attributes(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    fragment: SemanticSymbolId,
    target: SemanticSymbolId,
    location: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceCheckError> {
    let invalid = || SourceCheckError::Property(location);
    let namespace = store.get_parent_of_symbol(fragment).ok_or_else(invalid)?;
    let owner = store.symbol(target).ok_or_else(invalid)?;
    let call = owner
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::Call.as_ref()))
        .and_then(|call| store.get_merged_symbol(call))
        .ok_or_else(invalid)?;
    let record = store.symbol(call).ok_or_else(invalid)?;
    let Some([declaration]) = record.declarations() else {
        return Err(invalid());
    };
    let declaration = *declaration;
    let declaration_record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::CallSignatureDeclaration(signature) = &declaration_record.data else {
        return Err(invalid());
    };
    let [props, context] = signature.parameters.nodes.as_slice() else {
        return Err(invalid());
    };
    let props = child_ref(declaration, *props);
    let props_record = host.node(props).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter) = &props_record.data else {
        return Err(invalid());
    };
    let context = child_ref(declaration, *context);
    let context_record = host.node(context).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(context_parameter) = &context_record.data else {
        return Err(invalid());
    };
    let annotation = parameter
        .type_
        .map(|annotation| child_ref(props, annotation))
        .ok_or_else(invalid)?;
    let annotation_record = host.node(annotation).ok_or_else(invalid)?;
    let NodeData::IntersectionTypeNode(intersection) = &annotation_record.data else {
        return Err(invalid());
    };
    let [parameter_type, attributes] = intersection.types.nodes.as_slice() else {
        return Err(invalid());
    };
    let parameter_type = child_ref(annotation, *parameter_type);
    let parameter_record = host.node(parameter_type).ok_or_else(invalid)?;
    let NodeData::TypeReferenceNode(parameter_reference) = &parameter_record.data else {
        return Err(invalid());
    };
    let parameter_name = child_ref(parameter_type, parameter_reference.type_name);
    let parameter_name_record = host.node(parameter_name).ok_or_else(invalid)?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(invalid());
    };
    let attributes = child_ref(annotation, *attributes);
    let attributes_record = host.node(attributes).ok_or_else(invalid)?;
    let NodeData::TypeLiteralNode(literal) = &attributes_record.data else {
        return Err(invalid());
    };
    let [property] = literal.members.nodes.as_slice() else {
        return Err(invalid());
    };
    let property = child_ref(attributes, *property);
    let property_record = host.node(property).ok_or_else(invalid)?;
    let (child_name, child_annotation, postfix) = match &property_record.data {
        NodeData::PropertyDeclaration(children)
            if property_record.kind == SyntaxKind::PropertyDeclaration
                && children.initializer.is_none()
                && children.symbol.is_none()
                && children.facts == 0
                && children.modifiers.is_none() =>
        {
            (
                children.name,
                children.type_.ok_or_else(invalid)?,
                children.postfix_token,
            )
        }
        NodeData::PropertySignatureDeclaration(children)
            if property_record.kind == SyntaxKind::PropertySignature
                && children.symbol.is_none()
                && children.modifiers.is_none() =>
        {
            (children.name, children.type_, children.postfix_token)
        }
        _ => return Err(invalid()),
    };
    let postfix = postfix
        .map(|postfix| child_ref(property, postfix))
        .ok_or_else(invalid)?;
    let postfix_record = host.node(postfix).ok_or_else(invalid)?;
    let name = child_ref(property, child_name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let child_type = child_ref(property, child_annotation);
    let child_record = host.node(child_type).ok_or_else(invalid)?;
    let NodeData::TypeReferenceNode(child_reference) = &child_record.data else {
        return Err(invalid());
    };
    let child_name = child_ref(child_type, child_reference.type_name);
    let child_name_record = host.node(child_name).ok_or_else(invalid)?;
    let NodeData::Identifier(child_identifier) = &child_name_record.data else {
        return Err(invalid());
    };
    let react_node = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("ReactNode"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    if owner.name().as_utf8() != Some("StatelessComponent")
        || store.get_parent_of_symbol(target) != Some(namespace)
        || record.flags() != SymbolFlags::SIGNATURE
        || record.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(call) != Some(target)
        || !host.symbol_matches(store, declaration, call)
        || declaration_record.kind != SyntaxKind::CallSignature
        || props_record.kind != SyntaxKind::Parameter
        || props_record.parent != Some(declaration.node)
        || parameter.question_token.is_some()
        || context_record.kind != SyntaxKind::Parameter
        || context_record.parent != Some(declaration.node)
        || context_parameter.question_token.is_none()
        || annotation_record.kind != SyntaxKind::IntersectionType
        || annotation_record.parent != Some(props.node)
        || intersection.types.has_trailing_comma
        || parameter_record.kind != SyntaxKind::TypeReference
        || parameter_record.parent != Some(annotation.node)
        || parameter_reference.type_arguments.is_some()
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.parent != Some(parameter_type.node)
        || parameter_identifier.text != "P"
        || attributes_record.kind != SyntaxKind::TypeLiteral
        || attributes_record.parent != Some(annotation.node)
        || literal.members.has_trailing_comma
        || property_record.flags.0 != 0
        || property_record.parent != Some(attributes.node)
        || postfix_record.kind != SyntaxKind::QuestionToken
        || postfix_record.flags.0 != 0
        || postfix_record.parent != Some(property.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(property.node)
        || identifier.text != "children"
        || child_record.kind != SyntaxKind::TypeReference
        || child_record.parent != Some(property.node)
        || child_reference.type_arguments.is_some()
        || child_name_record.kind != SyntaxKind::Identifier
        || child_name_record.parent != Some(child_type.node)
        || child_identifier.text != "ReactNode"
        || store
            .symbol(react_node)
            .is_none_or(|record| !record.flags().contains(SymbolFlags::TYPE_ALIAS))
        || store.get_parent_of_symbol(react_node) != Some(namespace)
    {
        return Err(invalid());
    }

    CanonicalTypeQuery::new(store, host, options, diagnostics)?
        .get_type_from_type_node(attributes)
        .map_err(Into::into)
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

#[allow(clippy::too_many_arguments)] // Dynamic intrinsic tags retain their source and runtime facts.
fn resolve_intrinsic_component_tag(
    store: &mut CanonicalTypeMapperStore,
    bound: &BoundFile,
    namespace: &JsxNamespace,
    opening: NodeRef,
    tag: &JsxTagPlan,
    names: &[String],
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(TypeId, SignatureId), SourceCheckError> {
    let mut attributes = Vec::with_capacity(names.len());
    for name in names {
        let intrinsic = resolve_intrinsic_tag(
            store,
            bound,
            namespace,
            opening,
            &JsxTagPlan {
                node: tag.node,
                name: name.clone(),
                intrinsic: true,
                namespace_member: None,
            },
            options,
            diagnostics,
        )?;
        if !attributes.contains(&intrinsic.attributes_type) {
            attributes.push(intrinsic.attributes_type);
        }
    }
    let attributes = match attributes.as_slice() {
        [attributes] => *attributes,
        [] => return Err(SourceCheckError::Call(opening)),
        _ => store
            .canonical_intersection_type(&attributes, None)
            .map_err(|_| unsupported(opening, SyntaxKind::JsxOpeningElement))?,
    };
    let signature = intrinsic_signature(store, opening, attributes, namespace.element_type)?;
    Ok((attributes, signature))
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
        if let Some(type_) = store
            .type_node_links(initializer)
            .and_then(|links| links.resolved_type)
            && jsx_intrinsic_component_names(store, type_).is_some()
        {
            return Ok(type_);
        }
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
    let (JsxScalarPlan::Identifier { node, .. }
    | JsxScalarPlan::Property { node, .. }
    | JsxScalarPlan::Call { node, .. }) = &spread.value
    else {
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
    let expected = jsx_expected_attribute_property(
        store,
        expected_attributes,
        &attribute.name,
        attribute.node,
    )?
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
        JsxScalarPlan::Array { node, elements } => {
            let global_types = source
                .3
                .ok_or_else(|| unsupported(*node, SyntaxKind::ArrayLiteralExpression))?;
            let mut types = Vec::with_capacity(elements.len());
            for element in elements {
                types.push(execute_scalar(
                    store,
                    source,
                    namespace,
                    element,
                    options,
                    diagnostics,
                )?);
            }
            let element = store.expression_union_type_with_global_types(
                global_types,
                &types,
                UnionReduction::Subtype,
            )?;
            let array = store.create_canonical_array_type(global_types, element, false)?;
            (*node, store.create_array_literal_type(global_types, array)?)
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
                        .or_else(|| {
                            let initializer = child_ref(declaration, variable.initializer?);
                            let initializer_record = arena.get(initializer.node)?;
                            if initializer_record.kind != SyntaxKind::ArrowFunction {
                                return None;
                            }
                            jsx_component_value_type(store, arena, bound, symbol, *node).ok()
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
        JsxScalarPlan::Call {
            node,
            callee,
            arguments,
        } => {
            let callee_type =
                execute_scalar(store, source, namespace, callee, options, diagnostics)?;
            if !arguments.is_empty() {
                let global_types = source
                    .3
                    .ok_or_else(|| unsupported(*node, SyntaxKind::CallExpression))?;
                let mut argument_types = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    argument_types.push(execute_scalar(
                        store,
                        source,
                        namespace,
                        argument,
                        options,
                        diagnostics,
                    )?);
                }
                let signature = resolve_jsx_spread_call_signature(
                    store,
                    host,
                    global_types,
                    options,
                    diagnostics,
                    *node,
                    callee_type,
                    &argument_types,
                )?;
                let type_ = store
                    .signature(signature)
                    .and_then(super::signatures::Signature::resolved_return_type)
                    .ok_or(SourceCheckError::Call(*node))?;
                publish_signature_links(store, *node, signature)?;
                publish_type_links(store, *node, type_)?;
                return Ok(type_);
            }
            let StoredCallableSetValidation::Valid { projection, .. } =
                validate_stored_callable_set(store, callee_type)
            else {
                return Err(unsupported(*node, SyntaxKind::CallExpression));
            };
            let [callable] = projection.call_signatures.as_ref() else {
                return Err(unsupported(*node, SyntaxKind::CallExpression));
            };
            let signature = callable.signature;
            let record = store
                .signature(signature)
                .ok_or(SourceCheckError::Call(*node))?;
            if !projection.construct_signatures.is_empty()
                || !record.type_parameters().is_empty()
                || record.this_parameter().is_some()
                || record.has_rest_parameter()
                || record.min_argument_count() != 0
                || !record.parameters().is_empty()
                || !callable.parameters.is_empty()
                || callable.min_argument_count != 0
                || callable.rest_parameter.is_some()
            {
                return Err(unsupported(*node, SyntaxKind::CallExpression));
            }
            let type_ = if let Some(type_) = callable.return_type {
                type_
            } else if let Some(global_types) = source.3 {
                CanonicalTypeQuery::new_with_global_types(
                    store,
                    host,
                    global_types,
                    options,
                    diagnostics,
                )?
                .get_return_type_of_signature(signature)?
            } else {
                CanonicalTypeQuery::new(store, host, options, diagnostics)?
                    .get_return_type_of_signature(signature)?
            };
            if store
                .signature(signature)
                .and_then(super::signatures::Signature::resolved_return_type)
                != Some(type_)
            {
                return Err(SourceCheckError::Call(*node));
            }
            publish_signature_links(store, *node, signature)?;
            (*node, type_)
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
    global_types: Option<&CanonicalGlobalTypes>,
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
    let intersection = materialized_jsx_attribute_intersection(store, expected, opening)?;
    let expected_members = intersection
        .as_ref()
        .map_or(structured.members, |intersection| {
            Some(intersection.members)
        });
    let required = intersection.map_or_else(
        || structured.properties.clone().unwrap_or_default(),
        |intersection| intersection.properties,
    );
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
                    format_attribute_object(store, host, global_types, attributes, children)?,
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
                global_types,
                expected,
                name,
                opening,
                options,
                diagnostics,
            )?
            && !jsx_child_is_assignable(
                store,
                children.type_,
                expected_type,
                children.node,
                (host, global_types),
                options,
                diagnostics,
            )?
        {
            let display = jsx_child_assignability_display(
                store,
                host,
                global_types,
                children.type_,
                expected_type,
            )?;
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
                let source =
                    format_attribute_object(store, host, global_types, attributes, children)?;
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

fn materialized_jsx_attribute_intersection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    location: NodeRef,
) -> Result<Option<super::intersection_types::IntersectionTypeProjection>, SourceCheckError> {
    let record = store
        .type_payload(type_)
        .ok_or(SourceCheckError::Property(location))?;
    if !matches!(
        record.data(),
        super::TypeData::Intersection(intersection)
            if intersection.intersection.property_cache.is_some()
    ) {
        return Ok(None);
    }
    store
        .validate_intersection_type(type_)
        .map(Some)
        .map_err(|_| SourceCheckError::Property(location))
}

fn jsx_expected_attribute_property(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    name: &str,
    location: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let intersection = materialized_jsx_attribute_intersection(store, type_, location)?;
    let members = intersection.map_or_else(
        || {
            store
                .type_payload(type_)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
        },
        |intersection| Some(intersection.members),
    );
    Ok(members
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(name)))
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
    global_types: Option<&CanonicalGlobalTypes>,
    attributes: &[CheckedJsxAttribute],
    children: Option<CheckedJsxChildren>,
) -> Result<String, SourceCheckError> {
    if attributes.is_empty() && children.is_none() {
        return Ok("{}".to_owned());
    }
    let format_type = |type_: TypeId| {
        if let Some(global_types) = global_types {
            type_to_string_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                type_,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )
        } else {
            type_to_string_with_host_and_flags(
                store,
                host,
                type_,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )
        }
    };
    let mut names = attributes
        .iter()
        .map(|attribute| -> Result<String, SourceCheckError> {
            let name = if attribute.plan.name.contains(':') {
                format!("\"{}\"", attribute.plan.name)
            } else {
                attribute.plan.name.clone()
            };
            Ok(format!("{name}: {};", format_type(attribute.type_)?))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(children) = children {
        names.push(format!(
            "{}: {};",
            checked_jsx_children_name(store, children)?,
            format_type(children.type_)?
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

/// Checks rejected intrinsic type arguments without hiding missing nested names.
fn check_intrinsic_type_argument(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    parent: NodeRef,
    argument: NodeRef,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), SourceCheckError> {
    let result = if let Some(global_types) = global_types {
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
            .get_type_from_type_node(argument)
    } else {
        CanonicalTypeQuery::new(store, host, options, diagnostics)?
            .get_type_from_type_node(argument)
    };
    match result {
        Ok(_) => Ok(()),
        Err(super::DeclaredTypeError::TypeNodeUnavailable(
            super::type_nodes::TypeNodeUnavailable::MissingTypeReference(missing),
        )) if missing == argument => {
            let record = host
                .node(argument)
                .ok_or(SourceCheckError::Property(argument))?;
            let NodeData::TypeReferenceNode(reference) = &record.data else {
                return Err(SourceCheckError::Property(argument));
            };
            let name = child_ref(argument, reference.type_name);
            let name_record = host.node(name).ok_or(SourceCheckError::Property(name))?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(SourceCheckError::Property(name));
            };
            if record.kind != SyntaxKind::TypeReference
                || record.flags.0 != 0
                || record.parent != Some(parent.node)
                || name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(argument.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || reference.type_arguments.as_ref().is_some_and(|arguments| {
                    arguments.nodes.is_empty() || arguments.has_trailing_comma
                })
                || store
                    .type_node_links(argument)
                    .is_some_and(|links| links != &TypeNodeLinks::default())
                || [argument, name].into_iter().any(|node| {
                    store
                        .symbol_node_links(node)
                        .is_some_and(|links| links != &SymbolNodeLinks::default())
                })
            {
                return Err(SourceCheckError::Property(argument));
            }
            let nested = reference
                .type_arguments
                .as_ref()
                .map(|arguments| arguments.nodes.clone())
                .unwrap_or_default();
            let text = identifier.text.clone();
            add_diagnostic(diagnostics, name, 2304, [text])?;
            for nested in nested {
                check_intrinsic_type_argument(
                    store,
                    host,
                    global_types,
                    argument,
                    child_ref(argument, nested),
                    options,
                    diagnostics,
                )?;
            }
            Ok(())
        }
        Err(error) => Err(error.into()),
    }
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

    const LEGACY_REACT_FRAGMENT_COMPONENT_DECLARATIONS: &str = concat!(
        "type ComponentType<P = {}> = ComponentClass<P> | StatelessComponent<P>; ",
        "interface ComponentClass<P = {}, S = any> { ",
        "new(props: P, context?: any): ReactElement; } ",
        "interface StatelessComponent<P = {}> { ",
        "(props: P & { children?: ReactNode; }, context?: any): ReactElement | null; ",
        "} ",
        "const Fragment: ComponentType; ",
    );

    impl ReactFragmentFixture {
        fn new(source: &str, file: FileId, runtime: CanonicalJsxRuntime) -> Self {
            Self::with_fragment_declaration(
                source,
                file,
                runtime,
                concat!(
                    "interface ExoticComponent<P = {}> { (props: P): JSX.Element; } ",
                    "const Fragment: ExoticComponent<{ children?: ReactNode; }>; ",
                ),
            )
        }

        fn with_fragment_declaration(
            source: &str,
            file: FileId,
            runtime: CanonicalJsxRuntime,
            fragment_declaration: &str,
        ) -> Self {
            let library_source = [
                "declare namespace React { ",
                "interface ReactElement { marker: string; } ",
                "type ReactNode = ReactElement | string | number | boolean | null | undefined; ",
                fragment_declaration,
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement {} ",
                "interface ElementChildrenAttribute { children: {}; } ",
                "interface IntrinsicElements { ",
                "main: { children?: React.ReactNode; }; div: {}; span: {}; ",
                "} }",
            ]
            .concat();
            Self::with_library(source, file, runtime, &library_source)
        }

        fn with_library(
            source: &str,
            file: FileId,
            runtime: CanonicalJsxRuntime,
            library: &str,
        ) -> Self {
            let library: &'static ParseResult = Box::leak(Box::new(parse_source_file(library)));
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
    fn legacy_react_component_type_fragments_preserve_children_and_warm_identity() {
        let mut fixture = ReactFragmentFixture::with_library(
            concat!(
                "const invalidChild = () => 'invalid'; ",
                "const valid = <><div /></>; ",
                "const invalid = <>{invalidChild}</>; ",
                "const explicit = <React.Fragment><div /></React.Fragment>;",
            ),
            FileId::new(8_197),
            CanonicalJsxRuntime::Classic,
            concat!(
                "declare namespace React { ",
                "interface ReactElement { marker: string; } ",
                "type ReactNode = ReactElement | string | number | boolean | null | undefined; ",
                "interface ComponentClass<P = {}, S = any> { ",
                "new(props: P, context?: any): ReactElement; } ",
                "interface StatelessComponent<P = {}> { ",
                "(props: P & { children?: ReactNode }, context?: any): ReactElement | null; ",
                "propTypes?: { value?: P }; ",
                "contextTypes?: { value?: any }; ",
                "defaultProps?: P; ",
                "displayName?: string; } ",
                "type ComponentType<P = {}> = ComponentClass<P> | StatelessComponent<P>; ",
                "const Fragment: ComponentType; ",
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement {} ",
                "interface ElementChildrenAttribute { children: {}; } ",
                "interface IntrinsicElements { div: {}; } }",
            ),
        );

        let library_file = FileId::new(u32::try_from(fixture.file.index()).unwrap() + 1_000);
        let (library, _) = fixture.context.file(library_file).unwrap();
        assert!(library.iter().any(|(_, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return false;
            };
            let Some(NodeData::Identifier(name)) =
                library.get(property.name).map(|name| &name.data)
            else {
                return false;
            };
            name.text == "children"
                && record
                    .parent
                    .and_then(|parent| library.get(parent))
                    .is_some_and(|parent| {
                        parent.kind == SyntaxKind::TypeLiteral
                            && parent
                                .parent
                                .and_then(|parent| library.get(parent))
                                .is_some_and(|parent| parent.kind == SyntaxKind::IntersectionType)
                    })
        }));

        fixture.context.check_source_file(fixture.file).unwrap();

        let [diagnostic] = fixture.context.diagnostics().as_slice() else {
            panic!("only the callable legacy fragment child must report TS2322")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert!(
            diagnostic
                .diagnostic
                .render()
                .unwrap()
                .contains("ReactNode")
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
        let component = fixture
            .context
            .store()
            .value_symbol_links(fragment)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let reference = validate_direct_generic_reference(fixture.context.store(), component)
            .expect("legacy Fragment must retain its authenticated callable branch");
        let owner = fixture
            .context
            .store()
            .type_payload(reference.target)
            .and_then(super::super::type_records::TypeRecord::symbol)
            .unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(owner)
                .and_then(|record| record.name().as_utf8()),
            Some("StatelessComponent"),
        );
        let members = fixture
            .context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.context.store().symbol_table(members))
            .unwrap();
        for name in ["propTypes", "contextTypes", "defaultProps", "displayName"] {
            let property = members.get_source(name).unwrap();
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(property)
                    .is_none()
            );
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
    fn legacy_react_fragments_accept_generic_jsx_element_heritage() {
        let mut fixture = ReactFragmentFixture::with_library(
            "const view = <><div></div></>;",
            FileId::new(8_199),
            CanonicalJsxRuntime::Classic,
            concat!(
                "declare namespace React { ",
                "interface ReactElement<Props> { props: Props; } ",
                "type ReactText = string | number; ",
                "type ReactChild = ReactElement<any> | ReactText; ",
                "type ReactNode = ReactChild | boolean | null | undefined; ",
                "interface ComponentClass<P = {}, S = any> { ",
                "new(props: P, context?: any): ReactElement<any>; } ",
                "interface StatelessComponent<P = {}> { ",
                "(props: P & { children?: ReactNode; }, context?: any): ",
                "ReactElement<any> | null; } ",
                "type ComponentType<P = {}> = ComponentClass<P> | StatelessComponent<P>; ",
                "const Fragment: ComponentType; ",
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement<any> {} ",
                "interface ElementChildrenAttribute { children: {}; } ",
                "interface IntrinsicElements { div: {}; } }",
            ),
        );

        fixture.context.check_source_file(fixture.file).unwrap();
        assert!(fixture.context.diagnostics().is_empty());

        let globals = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .globals;
        let jsx = fixture
            .context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("JSX"))
            .unwrap();
        let element = fixture
            .context
            .store()
            .symbol(jsx)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Element"))
            .unwrap();
        let element = fixture
            .context
            .store()
            .declared_type_links(element)
            .and_then(|links| links.declared_type)
            .unwrap();
        let super::super::TypeData::Interface(interface) = fixture
            .context
            .store()
            .type_payload(element)
            .unwrap()
            .data()
        else {
            panic!("JSX.Element must retain its authenticated interface shell")
        };
        assert!(!interface.base_types_resolved);

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        fixture.context.recheck_source_file(fixture.file).unwrap();
        assert!(fixture.context.diagnostics().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
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
    fn unchecked_global_umd_jsx_aliases_are_boundaries_without_hiding_poisoned_links() {
        let library = parse_source_file(concat!(
            "export = React; ",
            "export as namespace React; ",
            "declare namespace React { export const Fragment: any; }",
        ));
        let consumer = parse_jsx_source_file("const view = <React.Fragment />;");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(
            consumer.diagnostics.is_empty(),
            "{:?}",
            consumer.diagnostics
        );
        let library_file = FileId::new(8_195);
        let consumer_file = FileId::new(8_196);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, declaration, state) in [
            (&library, library_file, true, CanonicalModuleState::External),
            (
                &consumer,
                consumer_file,
                false,
                CanonicalModuleState::Script,
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.tsx\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = crate::semantic::CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (library_file, &library.arena),
                (consumer_file, &consumer.arena),
            ],
            CanonicalCheckerOptions {
                jsx_runtime: CanonicalJsxRuntime::Classic,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let globals = context.store().intrinsic_bootstrap().unwrap().globals;
        let alias = context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("React"))
            .unwrap();
        let location = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    &record.data,
                    NodeData::Identifier(identifier) if identifier.text == "React"
                )
                .then_some(NodeRef::new(consumer.arena.id(), consumer_file, node))
            })
            .unwrap();
        assert!(context.store().alias_symbol_links(alias).is_none());
        let cold = context.store().checker_link_allocated_lengths();

        assert_eq!(
            resolve_local_jsx_namespace_alias(context.store(), alias, location),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node: location,
                    kind: SyntaxKind::Identifier,
                    role: SourceSyntaxRole::VariableInitializer,
                }
            )),
        );
        assert_eq!(context.store().checker_link_allocated_lengths(), cold);

        let declaration = context
            .store()
            .symbol(alias)
            .unwrap()
            .declarations()
            .unwrap()[0];
        assert!(context.store_mut_for_test().set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                type_only_declaration: Some(declaration),
                ..AliasSymbolLinks::default()
            },
        ));
        assert_eq!(
            resolve_local_jsx_namespace_alias(context.store(), alias, location),
            Err(SourceCheckError::Import(location)),
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
    fn legacy_react_fragment_component_types_are_authenticated_and_resolved() {
        let mut fixture = ReactFragmentFixture::with_fragment_declaration(
            "const view = <><div /></>;",
            FileId::new(8_197),
            CanonicalJsxRuntime::Classic,
            LEGACY_REACT_FRAGMENT_COMPONENT_DECLARATIONS,
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
        let exports = fixture.context.store().symbol(namespace).unwrap().exports();
        let exports = exports
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .unwrap();
        let alias = exports.get_source("ComponentType").unwrap();
        let fragment = exports.get_source("Fragment").unwrap();
        let declaration = fixture
            .context
            .store()
            .symbol(fragment)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .unwrap();
        let (arena, _) = fixture.context.file(declaration.file).unwrap();
        let NodeData::VariableDeclaration(variable) = &arena.get(declaration.node).unwrap().data
        else {
            panic!("React.Fragment must retain its ambient variable declaration")
        };
        let annotation = child_ref(declaration, variable.type_.unwrap());

        fixture.context.check_source_file(fixture.file).unwrap();

        assert!(fixture.context.diagnostics().is_empty());
        assert!(fixture.context.store().type_alias_links(alias).is_none());
        let component = fixture
            .context
            .store()
            .value_symbol_links(fragment)
            .and_then(|links| links.resolved_type)
            .expect("the authenticated fragment must publish its callable branch");
        assert_eq!(
            fixture
                .context
                .store()
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type),
            Some(component),
        );
        let reference = validate_direct_generic_reference(fixture.context.store(), component)
            .expect("React.Fragment must retain an authenticated generic reference");
        let owner = fixture
            .context
            .store()
            .type_payload(reference.target)
            .and_then(super::super::type_records::TypeRecord::symbol)
            .unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(owner)
                .and_then(|record| record.name().as_utf8()),
            Some("StatelessComponent"),
        );
    }

    #[test]
    fn legacy_react_fragment_component_types_reject_forged_alias_ownership() {
        let mut fixture = ReactFragmentFixture::with_fragment_declaration(
            "const view = <><div /></>;",
            FileId::new(8_198),
            CanonicalJsxRuntime::Classic,
            LEGACY_REACT_FRAGMENT_COMPONENT_DECLARATIONS,
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
        let alias = fixture
            .context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("ComponentType"))
            .unwrap();
        assert!(
            fixture
                .context
                .store_mut_for_test()
                .set_symbol_relationships(alias, None, None, None, None,)
        );

        assert!(matches!(
            fixture.context.check_source_file(fixture.file),
            Err(SourceCheckError::Property(_))
        ));
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
    fn missing_jsx_element_fragments_recover_any_and_preserve_nested_element_errors() {
        for runtime in [
            CanonicalJsxRuntime::Preserve,
            CanonicalJsxRuntime::Classic,
            CanonicalJsxRuntime::Automatic,
        ] {
            for no_implicit_any in [false, true] {
                let mut fixture =
                    RuntimeFixture::new("const view = <><div /><></></>;\n", FileId::new(8_220));
                let expression = fixture.expression("view");
                let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
                let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
                let host =
                    DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
                let options = CanonicalCheckerOptions {
                    no_implicit_any,
                    jsx_runtime: runtime,
                    ..CanonicalCheckerOptions::default()
                };
                let mut diagnostics = CanonicalCheckerDiagnostics::default();

                assert_eq!(
                    fixture
                        .store
                        .check_jsx_element(&host, expression, options, &mut diagnostics)
                        .unwrap(),
                    any,
                );
                assert_eq!(diagnostics.len(), usize::from(no_implicit_any));
                for diagnostic in diagnostics.as_slice() {
                    assert_eq!(diagnostic.diagnostic.code(), 7026);
                }
                for (node, record) in fixture.parsed.arena.iter() {
                    let expected = match record.kind {
                        SyntaxKind::JsxFragment => any,
                        SyntaxKind::JsxSelfClosingElement => error,
                        _ => continue,
                    };
                    let node = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                    assert_eq!(
                        fixture.store.type_node_links(node),
                        Some(&TypeNodeLinks {
                            resolved_type: Some(expected),
                            ..TypeNodeLinks::default()
                        }),
                    );
                }
                let cold = (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    diagnostics.as_slice().to_vec(),
                );

                assert_eq!(
                    fixture
                        .store
                        .check_jsx_element(&host, expression, options, &mut diagnostics)
                        .unwrap(),
                    any,
                );
                assert_eq!(
                    (
                        fixture.store.type_len(),
                        fixture.store.symbol_len(),
                        fixture.store.signature_len(),
                        fixture.store.checker_link_allocated_lengths(),
                        diagnostics.as_slice().to_vec(),
                    ),
                    cold,
                );
            }
        }
    }

    #[test]
    fn jsx_recovery_rejects_wrong_and_malformed_cached_types() {
        for source in ["const view = <></>;\n", "const view = <div />;\n"] {
            for malformed in [false, true] {
                let mut fixture = RuntimeFixture::new(source, FileId::new(8_221));
                let expression = fixture.expression("view");
                let host =
                    DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
                let options = CanonicalCheckerOptions::default();
                let mut diagnostics = CanonicalCheckerDiagnostics::default();
                let result = fixture
                    .store
                    .check_jsx_element(&host, expression, options, &mut diagnostics)
                    .unwrap();
                let poison = TypeNodeLinks {
                    resolved_type: Some(if malformed {
                        result
                    } else {
                        fixture.store.intrinsic_bootstrap().unwrap().number_type
                    }),
                    outer_type_parameters: malformed.then(Vec::new),
                };
                assert!(
                    fixture
                        .store
                        .set_type_node_links(expression, poison.clone())
                );
                let cold = (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    diagnostics.as_slice().to_vec(),
                );

                assert_eq!(
                    fixture
                        .store
                        .check_jsx_element(&host, expression, options, &mut diagnostics),
                    Err(SourceCheckError::Property(expression)),
                );
                assert_eq!(fixture.store.type_node_links(expression), Some(&poison));
                assert_eq!(
                    (
                        fixture.store.type_len(),
                        fixture.store.symbol_len(),
                        fixture.store.signature_len(),
                        fixture.store.checker_link_allocated_lengths(),
                        diagnostics.as_slice().to_vec(),
                    ),
                    cold,
                );
            }
        }
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
    #[allow(clippy::too_many_lines)] // Keep React declaration checking, intrinsic errors, and warm identity together.
    fn intrinsic_elements_keep_defaulted_react_component_class_references_lazy() {
        let source = concat!(
            "const first = <div<   number> label='ready' />;\n",
            "const second = <div<\n    number> label='ready' />;\n",
        );
        let mut fixture = ReactFragmentFixture::with_library(
            source,
            FileId::new(8_204),
            CanonicalJsxRuntime::Preserve,
            concat!(
                "declare namespace React { ",
                "type ComponentState = any; ",
                "type Ref<T> = T; ",
                "type SFC<P = {}> = P; ",
                "interface Component<P, S> {} ",
                "interface ComponentClass<P = {}, S = ComponentState> { ",
                "new(props: P): Component<P, S>; ",
                "displayName?: string; ",
                "} ",
                "interface ReactElement<P> { ",
                "type: string | ComponentClass<P> | SFC<P>; props: P; key: string; ",
                "} ",
                "interface ComponentElement<P, T extends Component<P, ComponentState>> ",
                "extends ReactElement<P> { type: ComponentClass<P>; ref?: Ref<T>; } ",
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement<any> {} ",
                "interface IntrinsicElements { div: { label: string }; } ",
                "}",
            ),
        );
        let library_file = FileId::new(u32::try_from(fixture.file.index()).unwrap() + 1_000);

        fixture.context.check_source_file(library_file).unwrap();
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
        let exports = fixture
            .context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .unwrap();
        let [component_class, react_element, component_element] =
            ["ComponentClass", "ReactElement", "ComponentElement"].map(|name| {
                fixture
                    .context
                    .store()
                    .symbol_table(exports)
                    .and_then(|exports| exports.get_source(name))
                    .unwrap()
            });
        let properties = [
            (component_class, "displayName"),
            (react_element, "type"),
            (component_element, "type"),
            (component_element, "ref"),
        ]
        .map(|(owner, name)| {
            fixture
                .context
                .store()
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| fixture.context.store().symbol_table(members))
                .and_then(|members| members.get_source(name))
                .unwrap()
        });
        for property in properties {
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(property)
                    .is_none()
            );
        }

        fixture.context.check_source_file(fixture.file).unwrap();

        assert_eq!(fixture.context.diagnostics().len(), 2);
        for diagnostic in fixture.context.diagnostics().as_slice() {
            assert_eq!(diagnostic.diagnostic.code(), 2558);
            let range = diagnostic.range_override.unwrap().range();
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(&source[start..end], "number");
        }
        for owner in [component_class, react_element, component_element] {
            let type_ = fixture
                .context
                .store()
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let super::super::TypeData::Interface(interface) =
                fixture.context.store().type_payload(type_).unwrap().data()
            else {
                panic!("React component interfaces must preserve their declared identities")
            };
            assert!(!interface.declared_members_resolved);
        }
        for property in properties {
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(property)
                    .is_none()
            );
        }

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().index_info_len(),
            fixture.context.store().checker_link_allocated_lengths(),
            fixture.context.diagnostics().as_slice().to_vec(),
        );
        fixture.context.recheck_source_file(library_file).unwrap();
        fixture.context.recheck_source_file(fixture.file).unwrap();
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().index_info_len(),
                fixture.context.store().checker_link_allocated_lengths(),
                fixture.context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
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
    #[allow(clippy::too_many_lines)] // Keep nested missing names, TS2558 ranges, and warm caches together.
    fn intrinsic_type_arguments_check_references_and_preserve_exact_diagnostics() {
        let source = concat!(
            "type Existing = string;\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface IntrinsicElements { div: any; }\n",
            "}\n",
            "const primitive = <div<   number> />;\n",
            "const direct = <div< Missing>></div>;\n",
            "const nested = <div<Missing<AlsoMissing>> />;\n",
            "const named = <div<Existing> />;\n",
        );
        let mut fixture = RuntimeFixture::new(source, FileId::new(8_206));
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let namespace = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let existing = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Existing"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("JSX"), namespace),
            Some(None),
        );
        assert_eq!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("Existing"), existing),
            Some(None),
        );
        let primitive = fixture.expression("primitive");
        let direct = fixture.expression("direct");
        let nested = fixture.expression("nested");
        let named = fixture.expression("named");
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let options = CanonicalCheckerOptions {
            no_implicit_any: true,
            jsx_runtime: CanonicalJsxRuntime::Preserve,
            ..CanonicalCheckerOptions::default()
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [primitive, direct, nested, named] {
            fixture
                .store
                .check_jsx_element(&host, expression, options, &mut diagnostics)
                .unwrap();
        }

        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2558, 2304, 2558, 2304, 2304, 2558, 2558],
        );
        let missing = diagnostics
            .as_slice()
            .iter()
            .filter(|diagnostic| diagnostic.diagnostic.code() == 2304)
            .map(|diagnostic| {
                let NodeData::Identifier(name) = &fixture
                    .parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .data
                else {
                    panic!("the missing type name must own TS2304")
                };
                name.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(missing, ["Missing", "Missing", "AlsoMissing"]);
        let ranges = diagnostics
            .as_slice()
            .iter()
            .filter(|diagnostic| diagnostic.diagnostic.code() == 2558)
            .map(|diagnostic| {
                let range = diagnostic.range_override.unwrap().range();
                let start = usize::try_from(range.start.get()).unwrap();
                let end = usize::try_from(range.end.get()).unwrap();
                &source[start..end]
            })
            .collect::<Vec<_>>();
        assert_eq!(
            ranges,
            ["number", "Missing", "Missing<AlsoMissing>", "Existing"],
        );

        let references = fixture
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) =
                    &fixture.parsed.arena.get(reference.type_name)?.data
                else {
                    return None;
                };
                matches!(name.text.as_str(), "Existing" | "Missing" | "AlsoMissing").then_some((
                    name.text.as_str(),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    child_ref(
                        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                        reference.type_name,
                    ),
                ))
            })
            .collect::<Vec<_>>();
        let (_, named_argument, _) = references
            .iter()
            .find(|(name, _, _)| *name == "Existing")
            .copied()
            .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            fixture
                .store
                .type_node_links(named_argument)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
        assert_eq!(
            fixture
                .store
                .symbol_node_links(named_argument)
                .and_then(|links| links.resolved_symbol),
            Some(existing),
        );
        for (name, reference, identifier) in &references {
            if *name == "Existing" {
                continue;
            }
            assert!(fixture.store.type_node_links(*reference).is_none());
            assert!(fixture.store.symbol_node_links(*reference).is_none());
            assert!(fixture.store.symbol_node_links(*identifier).is_none());
        }
        let NodeData::JsxElement(direct_element) =
            &fixture.parsed.arena.get(direct.node).unwrap().data
        else {
            panic!("the direct missing reference belongs to a paired intrinsic element")
        };
        let direct_opening = child_ref(direct, direct_element.opening_element);
        let (_, missing_reference, missing_name) = references
            .iter()
            .find(|(name, reference, _)| {
                *name == "Missing"
                    && fixture
                        .parsed
                        .arena
                        .get(reference.node)
                        .is_some_and(|record| record.parent == Some(direct_opening.node))
            })
            .copied()
            .unwrap();

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        for expression in [primitive, direct, nested, named] {
            fixture
                .store
                .check_jsx_element(&host, expression, options, &mut diagnostics)
                .unwrap();
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
                diagnostics.as_slice().to_vec(),
            ),
            warm,
        );

        assert!(fixture.store.set_symbol_node_links(
            missing_name,
            SymbolNodeLinks {
                resolved_symbol: Some(existing),
            },
        ));
        let before = fixture.store.checker_link_allocated_lengths();
        assert!(matches!(
            fixture.store.check_jsx_element(
                &host,
                direct,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            ),
            Err(SourceCheckError::Property(node)) if node == missing_reference
        ));
        assert_eq!(fixture.store.checker_link_allocated_lengths(), before);
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
    #[allow(clippy::too_many_lines)] // Keep intersected props, index provenance, and warm caches together.
    fn overlapping_intrinsic_indexes_intersect_attributes_and_replay_warm() {
        let mut fixture = RuntimeFixture::new(
            concat!(
                "declare namespace JSX {\n",
                "  interface Element {}\n",
                "  interface IntrinsicElements {\n",
                "    [tag: string]: any;\n",
                "    [tag: `custom-${string}`]: { label: string };\n",
                "    [tag: `${string}-panel`]: { count: number };\n",
                "  }\n",
                "}\n",
                "const valid = <custom-panel label='ready' count={1} />;\n",
                "const invalid = <custom-panel label='ready' count='wrong' />;\n",
                "const missing = <custom-panel label='ready' />;\n",
                "const prefix = <custom-widget label='ready' />;\n",
                "const suffix = <plain-panel count={1} />;\n",
                "const fallback = <plain optional={1} />;\n",
            ),
            FileId::new(8_205),
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
        let valid = fixture.expression("valid");
        let invalid = fixture.expression("invalid");
        let missing = fixture.expression("missing");
        let prefix = fixture.expression("prefix");
        let suffix = fixture.expression("suffix");
        let fallback = fixture.expression("fallback");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for expression in [valid, invalid, missing, prefix, suffix, fallback] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }

        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2322);
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'.",
        );
        assert_eq!(diagnostics.as_slice()[1].diagnostic.code(), 2741);

        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let intrinsics = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("IntrinsicElements"))
            .unwrap();
        let intrinsic_type = fixture
            .store
            .declared_type_links(intrinsics)
            .and_then(|links| links.declared_type)
            .unwrap();
        let indexes = fixture
            .store
            .type_payload(intrinsic_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap();
        let [fallback_index, prefix_index, suffix_index] = indexes else {
            panic!("the intrinsic owner must retain its three declared indexes")
        };
        let declarations = [*fallback_index, *prefix_index, *suffix_index].map(|index| {
            fixture
                .store
                .index_info(index)
                .and_then(super::super::signatures::IndexInfo::declaration)
                .unwrap()
        });
        let overlapping = fixture
            .store
            .symbol_node_links(valid)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        let owner = fixture.store.symbol(overlapping).unwrap();
        assert_eq!(
            owner.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(owner.check_flags(), CheckFlags::INDEX_SYMBOL);
        assert_eq!(owner.declarations(), Some(declarations.as_slice()));
        assert_eq!(owner.value_declaration(), Some(declarations[0]));
        assert_eq!(owner.parent(), Some(intrinsics));
        let attributes = fixture
            .store
            .value_symbol_links(overlapping)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let intersection = fixture
            .store
            .validate_intersection_type(attributes)
            .unwrap();
        assert_eq!(intersection.types.len(), 2);
        for name in ["label", "count"] {
            assert!(
                fixture
                    .store
                    .symbol_table(intersection.members)
                    .and_then(|members| members.get_source(name))
                    .is_some()
            );
        }
        assert_eq!(
            fixture
                .store
                .jsx_element_links(valid)
                .and_then(|links| links.resolved_jsx_element_attributes_type),
            Some(attributes),
        );
        for expression in [valid, invalid, missing, prefix, suffix, fallback] {
            assert_eq!(
                fixture
                    .store
                    .jsx_element_links(expression)
                    .unwrap()
                    .jsx_flags,
                JsxFlags::INTRINSIC_INDEXED_ELEMENT,
            );
        }
        let individual_symbols = [*fallback_index, *prefix_index, *suffix_index].map(|index| {
            fixture
                .store
                .index_info(index)
                .and_then(super::super::signatures::IndexInfo::index_symbol)
                .unwrap()
        });
        assert!(!individual_symbols.contains(&overlapping));

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
            diagnostics.as_slice().to_vec(),
        );
        for expression in [valid, invalid, missing, prefix, suffix, fallback] {
            fixture.check(expression, CanonicalJsxRuntime::Preserve, &mut diagnostics);
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
                diagnostics.as_slice().to_vec(),
            ),
            warm,
        );

        assert!(fixture.store.set_symbol_declarations(
            overlapping,
            Some(vec![declarations[0]]),
            Some(declarations[0]),
        ));
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        assert!(matches!(
            fixture.store.check_jsx_element(
                &host,
                valid,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            ),
            Err(SourceCheckError::Property(node)) if node == valid
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
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
    #[allow(clippy::too_many_lines)] // Keep union inference, tag ownership, and warm caches together.
    fn string_union_component_tags_resolve_intrinsic_props_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface ElementChildrenAttribute { children: any; }\n",
            "  interface IntrinsicElements {\n",
            "    h1: { label: string; children?: string };\n",
            "    h2: { label: string; children?: string };\n",
            "  }\n",
            "}\n",
            "declare const Fixed: 'h1';\n",
            "const Heading = true ? 'h1' : 'h2';\n",
            "const single = <Fixed label='ready' />;\n",
            "const valid = <Heading label='ready'>title</Heading>;\n",
            "const invalid = <Heading label={1}>title</Heading>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_185);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/intrinsic-union.tsx\""),
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
            panic!("only the numeric heading label must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        let NodeData::Identifier(invalid_name) = &parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .data
        else {
            panic!("the invalid label must own its assignment diagnostic")
        };
        assert_eq!(invalid_name.text, "label");

        let (_, bound) = context.file(file).unwrap();
        let heading = bound
            .locals(bound.source_file())
            .and_then(|locals| context.store().symbol_table(locals))
            .and_then(|locals| locals.get_source("Heading"))
            .unwrap();
        let heading_type = context
            .store()
            .value_symbol_links(heading)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let mut heading_tags = 0;
        for (node, record) in parsed.arena.iter() {
            let NodeData::Identifier(name) = &record.data else {
                continue;
            };
            if name.text != "Heading"
                || record
                    .parent
                    .and_then(|parent| parsed.arena.get(parent))
                    .is_none_or(|parent| {
                        !matches!(
                            parent.kind,
                            SyntaxKind::JsxOpeningElement | SyntaxKind::JsxClosingElement
                        )
                    })
            {
                continue;
            }
            let node = NodeRef::new(parsed.arena.id(), file, node);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                Some(heading),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
                Some(heading_type),
            );
            heading_tags += 1;
        }
        assert_eq!(heading_tags, 4);

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
    #[allow(clippy::too_many_lines)] // Dynamic React tags retain lazy props, array child aliases, and warm state.
    fn intrinsic_union_components_preserve_global_react_child_array_capabilities() {
        let mut fixture = ReactFragmentFixture::with_library(
            concat!(
                "const Heading = true ? 'h1' : 'h2'; ",
                "const valid = <Heading className='ok' key='key'>{'Title'}</Heading>; ",
                "const invalid = <Heading className={1} key='key'>{'Title'}</Heading>;",
            ),
            FileId::new(8_244),
            CanonicalJsxRuntime::Preserve,
            concat!(
                "interface Array<T> {} ",
                "interface ReadonlyArray<T> {} ",
                "interface HTMLHeadingElement {} ",
                "declare namespace React { ",
                "interface ReactElement { marker: string; } ",
                "type ReactNode = string | number[]; ",
                "interface Attributes { key?: string; } ",
                "interface ClassAttributes<T> extends Attributes {} ",
                "interface DOMAttributes<T> {} ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { className?: string; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> {} ",
                "type DetailedHTMLProps<E extends HTMLAttributes<T>, T> = ClassAttributes<T> & E; ",
                "} ",
                "declare namespace JSX { ",
                "interface Element extends React.ReactElement {} ",
                "interface ElementChildrenAttribute { children: {}; } ",
                "interface IntrinsicElements { ",
                "h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>; ",
                "h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>; ",
                "} }",
            ),
        );

        fixture.context.check_source_file(fixture.file).unwrap();

        let [diagnostic] = fixture.context.diagnostics().as_slice() else {
            panic!("only the numeric className must produce a diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        assert_eq!(fixture.text(diagnostic.node.unwrap()), "className");

        let store = fixture.context.store();
        let react = store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("React"))
            .and_then(|namespace| store.get_merged_symbol(namespace))
            .unwrap();
        let exports = store
            .symbol(react)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .unwrap();
        let react_node = exports
            .get_source("ReactNode")
            .and_then(|alias| store.get_merged_symbol(alias))
            .unwrap();
        let children = store
            .type_alias_links(react_node)
            .and_then(|links| links.declared_type)
            .unwrap();
        let super::super::TypeData::Union(union) = store.type_payload(children).unwrap().data()
        else {
            panic!("ReactNode must retain its string and canonical array constituents")
        };
        assert!(union.union.types.iter().any(|type_| {
            store
                .canonical_array_reference(fixture.context.global_types(), *type_)
                .unwrap()
                .is_some()
        }));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        for (owner, name) in [("Attributes", "key"), ("HTMLAttributes", "className")] {
            let symbol = exports
                .get_source(owner)
                .and_then(|owner| store.get_merged_symbol(owner))
                .and_then(|owner| store.symbol(owner))
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source(name))
                .unwrap();
            assert_eq!(
                store
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type),
                Some(string),
            );
        }

        let warm = (
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
            fixture.context.diagnostics().as_slice().to_vec(),
        );
        fixture.context.recheck_source_file(fixture.file).unwrap();
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().mapper_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
                fixture.context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn namespaced_intrinsic_attributes_ignore_nonmatching_template_indexes() {
        let source = concat!(
            "interface Attributes {\n",
            "  [key: `do-${string}`]: number;\n",
            "  'ns:thing'?: string;\n",
            "}\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface IntrinsicElements { div: Attributes; }\n",
            "}\n",
            "const valid = <div ns:thing='ready' />;\n",
            "const matching = <div do-work={1} />;\n",
            "const wrongIndex = <div do-work='wrong' />;\n",
            "const wrongNamed = <div ns:thing={1} />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_186);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/namespaced-index.tsx\""),
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

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2322)
        );
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'.",
        );
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        let NodeData::JsxNamespacedName(name) = &parsed
            .arena
            .get(diagnostics[1].node.unwrap().node)
            .unwrap()
            .data
        else {
            panic!("the named-property mismatch must retain its complete namespaced name")
        };
        let NodeData::Identifier(namespace) = &parsed.arena.get(name.namespace).unwrap().data
        else {
            unreachable!("the namespaced attribute has an identifier namespace")
        };
        let NodeData::Identifier(local) = &parsed.arena.get(name.name).unwrap().data else {
            unreachable!("the namespaced attribute has an identifier local name")
        };
        assert_eq!(
            (namespace.text.as_str(), local.text.as_str()),
            ("ns", "thing"),
        );

        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().index_info_len(),
            context.store().checker_link_allocated_lengths(),
            diagnostics.to_vec(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().index_info_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            cold,
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
    #[allow(clippy::too_many_lines)] // Array child contexts share canonical targets and warm caches.
    fn function_component_array_children_use_their_contextual_element_types() {
        let source = concat!(
            "interface Array<T> {}\n",
            "interface ReadonlyArray<T> {}\n",
            "declare var React: any;\n",
            "declare namespace JSX {\n",
            "  interface Element { marker: string; }\n",
            "  interface ElementChildrenAttribute { children: {}; }\n",
            "  interface IntrinsicElements { span: {}; }\n",
            "}\n",
            "interface ArrayChildren { children: JSX.Element[]; }\n",
            "interface FlexibleChildren { children: JSX.Element | JSX.Element[]; }\n",
            "interface TextChildren { children: string[]; }\n",
            "interface MixedChildren { ",
            "children: string | JSX.Element | (string | JSX.Element)[]; }\n",
            "interface ReadonlyChildren { children: ReadonlyArray<JSX.Element>; }\n",
            "declare function ArrayComponent(props: ArrayChildren): any;\n",
            "declare function FlexibleComponent(props: FlexibleChildren): any;\n",
            "declare function MixedComponent(props: MixedChildren): any;\n",
            "declare function ReadonlyComponent(props: ReadonlyChildren): any;\n",
            "declare function TextComponent(props: TextChildren): any;\n",
            "const direct = <ArrayComponent><span /><span /></ArrayComponent>;\n",
            "const flexible = <FlexibleComponent><span /><span /></FlexibleComponent>;\n",
            "const mixed = <MixedComponent><span />ready</MixedComponent>;\n",
            "const readonly = <ReadonlyComponent><span /><span /></ReadonlyComponent>;\n",
            "const invalid = <TextComponent>ready{123}</TextComponent>;\n",
        );

        for (index, runtime) in [CanonicalJsxRuntime::Classic, CanonicalJsxRuntime::Preserve]
            .into_iter()
            .enumerate()
        {
            let parsed = parse_jsx_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_200 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/jsx-array-children.tsx\""),
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
                panic!("only the numeric array child must fail in {runtime:?} mode")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'.",
            );
            let range = parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            assert_eq!(
                source.get(range.start.get() as usize..range.end.get() as usize),
                Some("{123}"),
            );

            let element_type = context
                .store()
                .intrinsic_bootstrap()
                .and_then(|bootstrap| context.store().symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source("JSX"))
                .and_then(|namespace| context.store().symbol(namespace))
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| context.store().symbol_table(exports))
                .and_then(|exports| exports.get_source("Element"))
                .and_then(|symbol| context.store().declared_type_links(symbol))
                .and_then(|links| links.declared_type)
                .unwrap();
            let mut component_children = 0;
            for (node, record) in parsed.arena.iter() {
                let NodeData::JsxOpeningElement(opening_data) = &record.data else {
                    continue;
                };
                let opening = NodeRef::new(parsed.arena.id(), file, node);
                let NodeData::Identifier(tag) =
                    &parsed.arena.get(opening_data.tag_name).unwrap().data
                else {
                    panic!("the test component tags are direct identifiers")
                };
                let attributes = child_ref(opening, opening_data.attributes);
                let type_ = context
                    .store()
                    .type_node_links(attributes)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let children = context
                    .store()
                    .type_payload(type_)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.members)
                    .and_then(|members| context.store().symbol_table(members))
                    .and_then(|members| members.get_source("children"))
                    .unwrap();
                let child_type = context
                    .store()
                    .value_symbol_links(children)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let array = context
                    .store()
                    .canonical_array_reference(context.global_types(), child_type)
                    .unwrap()
                    .unwrap();
                if matches!(tag.text.as_str(), "FlexibleComponent" | "ReadonlyComponent") {
                    assert_eq!(array.element_type, element_type);
                }
                component_children += 1;
            }
            assert_eq!(component_children, 5);

            let cold = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                ),
                cold,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Tuple children retain indexed contexts and warm identities.
    fn function_component_tuple_children_use_their_contextual_position_types() {
        let source = concat!(
            "interface Array<T> {}\n",
            "interface ReadonlyArray<T> {}\n",
            "declare var React: any;\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface ElementChildrenAttribute { children: {}; }\n",
            "  interface IntrinsicElements { span: {}; }\n",
            "}\n",
            "interface PairChildren { children: [string, number]; }\n",
            "interface MixedChildren { children: [string, number] | boolean[]; }\n",
            "declare function Pair(props: PairChildren): any;\n",
            "declare function Mixed(props: MixedChildren): any;\n",
            "const pair = <Pair>ready{123}</Pair>;\n",
            "const mixed = <Mixed>ready{123}</Mixed>;\n",
            "const booleans = <Mixed>{true}{false}</Mixed>;\n",
            "const invalid = <Mixed>{(<span />) as unknown}{\"wrong\"}</Mixed>;\n",
        );

        for (index, runtime) in [CanonicalJsxRuntime::Classic, CanonicalJsxRuntime::Preserve]
            .into_iter()
            .enumerate()
        {
            let parsed = parse_jsx_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_202 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/jsx-tuple-children.tsx\""),
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

            let [first, second] = context.diagnostics().as_slice() else {
                panic!("both invalid tuple positions must fail in {runtime:?} mode")
            };
            for (diagnostic, expected_message, expected_source) in [
                (
                    first,
                    "Type 'unknown' is not assignable to type 'string | boolean'.",
                    "{(<span />) as unknown}",
                ),
                (
                    second,
                    "Type 'string' is not assignable to type 'number | boolean'.",
                    "{\"wrong\"}",
                ),
            ] {
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(diagnostic.diagnostic.render().unwrap(), expected_message);
                let range = parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .range;
                assert_eq!(
                    source.get(range.start.get() as usize..range.end.get() as usize),
                    Some(expected_source),
                );
            }

            let mut contextual_tuples = 0;
            for (_, record) in parsed.arena.iter() {
                let NodeData::JsxOpeningElement(opening) = &record.data else {
                    continue;
                };
                let attributes = NodeRef::new(parsed.arena.id(), file, opening.attributes);
                let attributes_type = context
                    .store()
                    .type_node_links(attributes)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let children = context
                    .store()
                    .type_payload(attributes_type)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.members)
                    .and_then(|members| context.store().symbol_table(members))
                    .and_then(|members| members.get_source("children"))
                    .unwrap();
                let children_type = context
                    .store()
                    .value_symbol_links(children)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let tuple = context
                    .store()
                    .canonical_tuple_shape(children_type)
                    .unwrap()
                    .expect("matching tuple contexts retain a canonical tuple identity");
                assert_eq!(tuple.element_types().len(), 2);
                assert!(
                    tuple
                        .element_infos()
                        .iter()
                        .all(|info| info.flags() == ElementFlags::REQUIRED)
                );
                contextual_tuples += 1;
            }
            assert_eq!(contextual_tuples, 4);

            let warm = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().canonical_tuple_target_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().canonical_tuple_target_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                ),
                warm,
            );
        }
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
    #[allow(clippy::too_many_lines)] // Inference, spread ownership, and warm publication share one graph.
    fn generic_jsx_components_infer_property_access_spreads_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX { interface Element {} }\n",
            "interface Props<T> { value: T; }\n",
            "interface NumberSource { props: Props<number>; }\n",
            "interface StringSource { props: Props<string>; }\n",
            "declare function Widget<T>(props: Props<T>): any;\n",
            "declare const numbers: NumberSource;\n",
            "declare const strings: StringSource;\n",
            "const numeric = <Widget {...numbers.props} />;\n",
            "const textual = <Widget {...strings.props} />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_188);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-jsx-property-spread.tsx\""),
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

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = [bootstrap.number_type, bootstrap.string_type];
        let mut checked = 0;
        for (node, record) in parsed.arena.iter() {
            let NodeData::JsxSelfClosingElement(element) = &record.data else {
                continue;
            };
            let opening = NodeRef::new(parsed.arena.id(), file, node);
            let signature = context
                .store()
                .signature_links(opening)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let callable = context.store().signature(signature).unwrap();
            assert!(callable.type_parameters().is_empty());
            let [parameter] = callable.parameters() else {
                panic!("the specialized JSX component must keep its one props parameter")
            };
            let props = context
                .store()
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let inferred = validate_direct_generic_reference(context.store(), props).unwrap();
            assert_eq!(inferred.type_arguments.as_slice(), &[expected[checked]]);

            let attributes = child_ref(opening, element.attributes);
            let NodeData::JsxAttributes(attribute_list) =
                &parsed.arena.get(attributes.node).unwrap().data
            else {
                panic!("the component must retain its JSX attributes")
            };
            let [spread] = attribute_list.properties.nodes.as_slice() else {
                panic!("the component must retain its one source spread")
            };
            let spread = child_ref(attributes, *spread);
            let NodeData::JsxSpreadAttribute(value) = &parsed.arena.get(spread.node).unwrap().data
            else {
                panic!("the JSX attribute must remain a spread")
            };
            let donor = child_ref(spread, value.expression);
            assert_eq!(
                parsed.arena.get(donor.node).unwrap().kind,
                SyntaxKind::PropertyAccessExpression,
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(donor)
                    .and_then(|links| links.resolved_type),
                Some(props),
            );
            let object_type = context
                .store()
                .type_node_links(attributes)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let member = context
                .store()
                .type_payload(object_type)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source("value"))
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(member)
                    .and_then(|links| links.resolved_type),
                Some(expected[checked]),
            );
            checked += 1;
        }
        assert_eq!(checked, expected.len());

        let warm = (
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
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Donor signatures, inferred props, and warm identities are one contract.
    fn generic_jsx_components_infer_zero_argument_call_spreads_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX { interface Element {} }\n",
            "interface Props<T> { value: T; }\n",
            "declare function Widget<T>(props: Props<T>): any;\n",
            "declare function numericProps(): Props<number>;\n",
            "declare function textualProps(): Props<string>;\n",
            "const numeric = <Widget {...numericProps()} />;\n",
            "const textual = <Widget {...textualProps()} />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_189);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-jsx-call-spread.tsx\""),
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

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = [bootstrap.number_type, bootstrap.string_type];
        let mut checked = 0;
        for (node, record) in parsed.arena.iter() {
            let NodeData::JsxSelfClosingElement(element) = &record.data else {
                continue;
            };
            let opening = NodeRef::new(parsed.arena.id(), file, node);
            let component_signature = context
                .store()
                .signature_links(opening)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let component = context.store().signature(component_signature).unwrap();
            assert!(component.type_parameters().is_empty());
            let [parameter] = component.parameters() else {
                panic!("the specialized component must retain its one props parameter")
            };
            let props = context
                .store()
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let inferred = validate_direct_generic_reference(context.store(), props).unwrap();
            assert_eq!(inferred.type_arguments.as_slice(), &[expected[checked]]);

            let attributes = child_ref(opening, element.attributes);
            let NodeData::JsxAttributes(attribute_list) =
                &parsed.arena.get(attributes.node).unwrap().data
            else {
                panic!("the component must retain its JSX attributes")
            };
            let [spread] = attribute_list.properties.nodes.as_slice() else {
                panic!("the component must retain its one call-result spread")
            };
            let spread = child_ref(attributes, *spread);
            let NodeData::JsxSpreadAttribute(value) = &parsed.arena.get(spread.node).unwrap().data
            else {
                panic!("the JSX attribute must remain a spread")
            };
            let call = child_ref(spread, value.expression);
            assert_eq!(
                parsed.arena.get(call.node).unwrap().kind,
                SyntaxKind::CallExpression,
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type),
                Some(props),
            );
            let donor_signature = context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let donor = context.store().signature(donor_signature).unwrap();
            assert!(donor.parameters().is_empty());
            assert_eq!(donor.resolved_return_type(), Some(props));
            checked += 1;
        }
        assert_eq!(checked, expected.len());

        let warm = (
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
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Donor arguments, inferred signatures, and warm caches share one graph.
    fn generic_jsx_components_infer_call_argument_spreads_and_replay_warm() {
        let source = concat!(
            "interface Array<T> {}\n",
            "interface ReadonlyArray<T> {}\n",
            "declare namespace JSX { interface Element {} }\n",
            "interface Props<T> { value: T; }\n",
            "declare function Widget<T>(props: Props<T>): any;\n",
            "declare function forward<T>(props: Props<T>): Props<T>;\n",
            "declare function select(names: readonly string[], props: Props<number>): Props<number>;\n",
            "declare const numbers: Props<number>;\n",
            "const direct = <Widget {...forward(numbers)} />;\n",
            "const selected = <Widget {...select(['value'], numbers)} />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_236);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-jsx-call-arguments.tsx\""),
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

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let mut calls = 0;
        for (node, record) in parsed.arena.iter() {
            let NodeData::CallExpression(call) = &record.data else {
                continue;
            };
            let node = NodeRef::new(parsed.arena.id(), file, node);
            let result = context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let inferred = validate_direct_generic_reference(context.store(), result).unwrap();
            assert_eq!(inferred.type_arguments.as_slice(), &[number]);
            let signature = context
                .store()
                .signature_links(node)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .signature(signature)
                    .and_then(super::super::signatures::Signature::resolved_return_type),
                Some(result),
            );
            if call.arguments.nodes.len() == 2 {
                let array = NodeRef::new(parsed.arena.id(), file, call.arguments.nodes[0]);
                let array_type = context
                    .store()
                    .type_node_links(array)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                assert!(
                    context
                        .store()
                        .canonical_array_reference(context.global_types(), array_type)
                        .unwrap()
                        .is_some_and(|array| array.array_literal)
                );
            }
            calls += 1;
        }
        assert_eq!(calls, 2);

        let warm = (
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
            warm,
        );
    }

    #[test]
    fn jsx_call_result_spreads_reject_unsupported_call_shapes_before_publication() {
        for (index, donor) in ["make().value()", "make<string>()", "make?.()"]
            .into_iter()
            .enumerate()
        {
            let source = format!(
                "declare function make(value?: number): any; \
                 declare const Widget: any; \
                 const view = <Widget {{...{donor}}} />;",
            );
            let fixture =
                RuntimeFixture::new(&source, FileId::new(8_220 + u32::try_from(index).unwrap()));
            let expression = fixture.expression("view");
            let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                fixture.store.preflight_jsx_element(&host, expression),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        kind: SyntaxKind::CallExpression,
                        ..
                    }
                ))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Constructor identity, child diagnostics, and warm caches stay linked.
    fn construct_only_jsx_components_check_props_and_children_without_new_signatures() {
        let source = concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface ElementChildrenAttribute { children: {}; } ",
            "}\n",
            "interface Props { label: string; children?: string; }\n",
            "declare const Widget: { new(props: Props): JSX.Element; };\n",
            "const valid = <Widget label=\"ready\">okay</Widget>;\n",
            "const invalidAttribute = <Widget label={123}>okay</Widget>;\n",
            "const invalidChild = <Widget label=\"ready\">{123}</Widget>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_187);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/construct-jsx-component.tsx\""),
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
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, expected) in diagnostics.iter().zip(["label", "{123}"]) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'.",
            );
            let range = parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            assert_eq!(
                source.get(range.start.get() as usize..range.end.get() as usize),
                Some(expected),
            );
        }

        let mut signatures = Vec::new();
        for (node, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::JsxOpeningElement {
                continue;
            }
            let opening = NodeRef::new(parsed.arena.id(), file, node);
            let signature = context
                .store()
                .signature_links(opening)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let constructor = context.store().signature(signature).unwrap();
            assert!(constructor.flags().contains(SignatureFlags::CONSTRUCT));
            assert_eq!(constructor.parameters().len(), 1);
            signatures.push(signature);
        }
        assert_eq!(signatures.len(), 3);
        assert!(
            signatures
                .iter()
                .all(|signature| *signature == signatures[0])
        );

        let warm = (
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
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Instance props, constructor identity, and diagnostics share one contract.
    fn class_jsx_components_select_element_attributes_property_and_replay_warm() {
        let source = concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface ElementAttributesProperty { props: {}; } ",
            "interface ElementChildrenAttribute { children: {}; } ",
            "}\n",
            "interface Props { label: string; children?: string; }\n",
            "interface Instance { props: Props; }\n",
            "declare const EmptyWidget: { new(): Instance; };\n",
            "declare const LegacyWidget: { new(value: { ignored: boolean }): Instance; };\n",
            "const empty = <EmptyWidget label=\"ready\">okay</EmptyWidget>;\n",
            "const legacy = <LegacyWidget label=\"ready\">okay</LegacyWidget>;\n",
            "const wrongAttribute = <EmptyWidget label={123}>okay</EmptyWidget>;\n",
            "const wrongChild = <LegacyWidget label=\"ready\">{123}</LegacyWidget>;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_230);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/jsx-instance-props.tsx\""),
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
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, expected) in diagnostics.iter().zip(["label", "{123}"]) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'.",
            );
            let range = parsed
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            assert_eq!(
                source.get(range.start.get() as usize..range.end.get() as usize),
                Some(expected),
            );
        }

        let mut constructors = Vec::new();
        for (node, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::JsxOpeningElement {
                continue;
            }
            let opening = NodeRef::new(parsed.arena.id(), file, node);
            let signature = context
                .store()
                .signature_links(opening)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let constructor = context.store().signature(signature).unwrap();
            assert!(constructor.flags().contains(SignatureFlags::CONSTRUCT));
            constructors.push(constructor.parameters().len());
        }
        assert_eq!(constructors, [0, 1, 0, 1]);

        let warm = (
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
            warm,
        );
    }

    #[test]
    fn class_jsx_components_report_missing_element_attributes_property() {
        let source = concat!(
            "declare namespace JSX { ",
            "interface Element {} ",
            "interface ElementAttributesProperty { props: {}; } ",
            "}\n",
            "interface Instance {}\n",
            "declare const Widget: { new(): Instance; };\n",
            "const invalid = <Widget label=\"ready\" />;\n",
        );
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_231);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/jsx-missing-instance-props.tsx\""),
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
            panic!("a missing instance props property must produce exactly one diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2607);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "JSX element class does not support attributes because it does not have a 'props' property.",
        );

        let warm = (
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
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve overload identity, tuple positions, and warm diagnostics.
    fn overloaded_construct_jsx_components_report_indexed_tuple_child_diagnostics() {
        let source = concat!(
            "interface Array<T> {}\n",
            "interface ReadonlyArray<T> {}\n",
            "declare var React: any;\n",
            "declare namespace JSX {\n",
            "  interface Element {}\n",
            "  interface ElementChildrenAttribute { children: {}; }\n",
            "  interface IntrinsicElements { div: {}; }\n",
            "}\n",
            "interface Props { children: [string, number] | boolean[]; }\n",
            "interface WidgetConstructor {\n",
            "  new(props: Props): JSX.Element;\n",
            "  new(props: Props, context: any): JSX.Element;\n",
            "}\n",
            "declare const Widget: WidgetConstructor;\n",
            "const valid = <Widget>ready{123}</Widget>;\n",
            "const invalid = <Widget>{(<div />) as unknown}{\"wrong\"}</Widget>;\n",
        );

        for (index, runtime) in [CanonicalJsxRuntime::Classic, CanonicalJsxRuntime::Preserve]
            .into_iter()
            .enumerate()
        {
            let parsed = parse_jsx_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_230 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/jsx-overloaded-tuple-children.tsx\""),
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

            let overload = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ConstructSignature).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .last()
                .expect("the component retains its final constructor overload");
            let [first, second] = context.diagnostics().as_slice() else {
                panic!("both invalid tuple positions must report TS2769 in {runtime:?} mode")
            };
            for (diagnostic, expected, expression) in [
                (
                    first,
                    concat!(
                        "No overload matches this call.\n",
                        "  The last overload gave the following error.\n",
                        "    Type 'unknown' is not assignable to type 'string | boolean'.",
                    ),
                    "{(<div />) as unknown}",
                ),
                (
                    second,
                    concat!(
                        "No overload matches this call.\n",
                        "  The last overload gave the following error.\n",
                        "    Type 'string' is not assignable to type 'number | boolean'.",
                    ),
                    "{\"wrong\"}",
                ),
            ] {
                assert_eq!(diagnostic.diagnostic.code(), 2769);
                assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
                let range = parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .range;
                assert_eq!(
                    source.get(range.start.get() as usize..range.end.get() as usize),
                    Some(expression),
                );
                let [related] = diagnostic.related_information.as_slice() else {
                    panic!("constructor failures must retain their final overload declaration")
                };
                assert_eq!(related.node, Some(overload));
                assert_eq!(related.diagnostic.code(), 2771);
                assert_eq!(
                    related.diagnostic.render().unwrap(),
                    "The last overload is declared here.",
                );
            }

            let selected = context
                .store()
                .signature_links(overload)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let record = context.store().signature(selected).unwrap();
            assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
            assert_eq!(record.parameters().len(), 2);
            assert_eq!(record.min_argument_count(), 2);
            for (node, record) in parsed.arena.iter() {
                if record.kind == SyntaxKind::JsxOpeningElement {
                    let opening = NodeRef::new(parsed.arena.id(), file, node);
                    assert_eq!(
                        context
                            .store()
                            .signature_links(opening)
                            .and_then(|links| links.resolved_signature.signature()),
                        Some(selected),
                    );
                }
            }

            let warm = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().canonical_tuple_target_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().canonical_tuple_target_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                ),
                warm,
            );
        }
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
