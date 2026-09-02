//! Exact source integration for admitted class and declared constructions.
//!
//! This includes `new Model()`, `new Model`, literal overload arguments, and
//! checked expression arguments for a direct local constructor, an explicit
//! source constructor, or an authenticated default-library construct value.
//! Generic source classes and named library constructors use the common
//! Construct selector and inference.
//! It follows pinned TypeScript-Go `checkCallExpression`,
//! `getResolvedSignature`, `resolveNewExpression`, and `resolveCall`.
//! An admitted constructor belongs to one preceding local class, an imported
//! exported ambient class, an earlier ambient variable, a named constructor
//! interface reached through an annotated ambient value, an authenticated class
//! constructor union, or a global `Object`, `Boolean`, `Array`, `Date`, or
//! `Promise` constructor. Imported ambient classes retain primitive constructor
//! arguments and canonical generic instantiations. Global arrays retain their
//! real length and generic-item overloads, including authenticated empty object
//! literals. Planning proves syntax, resolver routes, provider provenance, and
//! available cache facts before canonical declaration preparation. The source
//! expression checker validates argument semantics before New selection and
//! result publication.

use std::collections::{HashMap, HashSet};

mod global_error;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_jsnum::Number;

use super::{
    AliasTargetState, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, ClassError, DeclaredTypeError, DeclaredTypeHost,
    ResolvedSignatureState, SignatureId, SignatureLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::{CallableFamily, ValidatedSingleCallable},
    classes::{
        ClassBodyAccessToken, ClassConstructorVisibility, ClassMemberPlan, ClassMemberQueryPlan,
        ClassTypeQueryContext, SourceClassPlan, authenticated_class_constructor_value,
        completed_source_class_members, execute_nongeneric_class_member_query,
        optional_constructor_parameter_type, plan_nongeneric_class_member_query,
        preflight_nongeneric_class_member_query, source_class_plan_is_current,
    },
    conditional_types::ConditionalTypeError,
    constructor_values::{
        GlobalConstructorValueKind, GlobalConstructorValuePlan, plan_global_constructor_value,
        plan_global_generic_constructor_value, plan_global_named_constructor,
        plan_source_generic_constructor_value, prepare_global_constructor_candidates,
        resolve_global_constructor_candidates,
    },
    declared::{execute_type_parameter, preflight_class_or_interface_reference},
    functions::plan_function_type,
    generic_calls::{
        GenericCallVectorError, GenericCallVectorRequest, GenericConstructorContextMethod,
        PreparedGenericConstructorContext, demand_generic_call_vector_return_with_session,
        materialize_generic_call_vector_source, preflight_generic_class_constructor_signature,
    },
    generic_method_calls::{
        GenericMethodCallError, GenericMethodCallResolution, GenericMethodCallSelection,
        prepare_generic_constructor_context, resolve_generic_class_constructor,
        resolve_generic_class_constructor_with_context,
    },
    instantiate::InstantiationSession,
    jsdoc::leading_jsdoc_comment,
    object_members::{
        PropertyObjectPlan, PropertyObjectState, object_literal_state, plan_interface,
        plan_object_literal, plan_type_literal, publish_object_literal,
    },
    reference_types::{create_direct_generic_reference, validate_direct_generic_reference},
    signatures::{Signature, SignatureFlags},
    source::{CheckedExpressionTypes, PlannedExpression, PlannedExpressionKind},
    source_callables::{
        source_direct_call_argument_arrow_is_exact,
        source_promise_constructor_argument_arrow_is_exact,
    },
    source_imports::SourceImportBindingPlan,
    store::{CachedSignatureLookup, SourceNodeParent},
    type_nodes::{CanonicalTypeQuery, normalize_numeric_separators},
    type_records::{LiteralValue, StructuredTypeData, TypeCacheState, TypeRecord, type_list_key},
    types::{ObjectFlags, TypeFlags},
};

/// A valid construction form outside the exact default-class leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewUnsupported {
    Expression(NodeRef),
    Constructor(NodeRef),
    MissingArgumentList(NodeRef),
    Arguments(NodeRef),
    TypeArguments(NodeRef),
    ConstructorClass {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    ConstructorNotPrior {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
}

/// Malformed AST, binder, class, or checker-cache provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewInvariant {
    MissingNode(NodeRef),
    NameResolution {
        node: NodeRef,
        error: CanonicalNameResolutionError,
    },
    InvalidSymbol(SemanticSymbolId),
    DuplicatePlan(NodeRef),
    MergedSymbol {
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    InvalidClassPlan(NodeRef),
    InvalidConstructorCache(NodeRef),
    InvalidExpressionCache(NodeRef),
    InvalidClassValue(SemanticSymbolId),
    InvalidConstructSignature(SignatureId),
    Capacity(NodeRef),
}

/// Exact failure domain for direct default construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewError {
    Unsupported(SourceNewUnsupported),
    Invariant(SourceNewInvariant),
    DeclaredType(DeclaredTypeError),
    Class(ClassError),
    Call {
        node: NodeRef,
        error: super::calls::DirectCallError,
    },
}

impl SourceNewError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(unsupported) => Some(match unsupported {
                SourceNewUnsupported::Expression(node)
                | SourceNewUnsupported::Constructor(node)
                | SourceNewUnsupported::MissingArgumentList(node)
                | SourceNewUnsupported::Arguments(node)
                | SourceNewUnsupported::TypeArguments(node)
                | SourceNewUnsupported::ConstructorClass { node, .. }
                | SourceNewUnsupported::ConstructorNotPrior { node, .. } => node,
            }),
            Self::Invariant(invariant) => match invariant {
                SourceNewInvariant::MissingNode(node)
                | SourceNewInvariant::DuplicatePlan(node)
                | SourceNewInvariant::NameResolution { node, .. }
                | SourceNewInvariant::InvalidClassPlan(node)
                | SourceNewInvariant::InvalidConstructorCache(node)
                | SourceNewInvariant::InvalidExpressionCache(node)
                | SourceNewInvariant::Capacity(node) => Some(node),
                SourceNewInvariant::InvalidSymbol(_)
                | SourceNewInvariant::MergedSymbol { .. }
                | SourceNewInvariant::InvalidClassValue(_)
                | SourceNewInvariant::InvalidConstructSignature(_) => None,
            },
            Self::Class(error) => error.node(),
            Self::Call { node, .. } => Some(node),
            Self::DeclaredType(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceNewError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<ClassError> for SourceNewError {
    fn from(error: ClassError) -> Self {
        Self::Class(error)
    }
}

const fn unsupported(reason: SourceNewUnsupported) -> SourceNewError {
    SourceNewError::Unsupported(reason)
}

const fn invariant(reason: SourceNewInvariant) -> SourceNewError {
    SourceNewError::Invariant(reason)
}

fn trace_constructor_failure(
    stage: &'static str,
    expression: NodeRef,
    constructor: NodeRef,
    details: std::fmt::Arguments<'_>,
) {
    let _ = std::io::Write::write_fmt(
        &mut std::io::stderr().lock(),
        format_args!(
            "ts-rust-constructor-error stage={stage} expression={expression:?} constructor={constructor:?} {details}\n"
        ),
    );
}

/// Opaque syntax, resolver, and provider proof for one direct construction.
#[derive(Clone, Debug)]
pub(super) struct SourceDefaultNewPlan {
    node: NodeRef,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    target: SourceNewTarget,
    early_preparation: bool,
    type_arguments: Vec<SourceNewTypeArgument>,
    argument: Option<SourceNewArgument>,
    additional_arguments: Vec<SourceNewArgument>,
    parameter: Option<SourceNewParameter>,
    executor: Option<Box<PlannedExpression>>,
    expression_arguments: Option<SourceNewExpressionArguments>,
}

#[derive(Clone, Debug)]
struct SourceNewExpressionArguments {
    nodes: Vec<NodeRef>,
    expressions: Option<Vec<PlannedExpression>>,
}

#[derive(Clone, Debug)]
enum SourceNewTarget {
    Class(Box<ClassMemberQueryPlan>),
    ConstructorOverloads(Box<super::classes::SourceClassPlan>),
    SourceClass(Box<SourceClassPlan>),
    GenericSourceClass(SourceGenericClassNewPlan),
    GenericLibrary(SourceGenericLibraryNewPlan),
    ImportedClass(Box<SourceImportBindingPlan>),
    Declared(SourceDeclaredConstructorPlan),
    ClassUnion(SourceClassUnionConstructorPlan),
    GlobalObject(SourceGlobalObjectConstructorPlan),
    GlobalArray(SourceGlobalArrayConstructorPlan),
    GlobalDate(SourceGlobalDateConstructorPlan),
    DeclaredInterface(global_error::DeclaredConstructorPlan),
    Library(Box<GlobalConstructorValuePlan>),
    GlobalPromise(SourceGlobalPromiseConstructorPlan),
}

#[derive(Clone, Debug)]
struct SourceGenericClassNewPlan {
    class: Box<SourceClassPlan>,
    type_argument_nodes: Option<Vec<NodeRef>>,
}

#[derive(Clone, Debug)]
struct SourceGenericLibraryNewPlan {
    library: Box<GlobalConstructorValuePlan>,
    type_argument_nodes: Option<Vec<NodeRef>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceDeclaredConstructorPlan {
    annotation: NodeRef,
    declaration: NodeRef,
    parameter: Option<SourceNewParameter>,
    signature_parameter: Option<SourceNewParameter>,
    min_argument_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceClassUnionConstructorPlan {
    provider: SourceClassUnionConstructorProvider,
    classes: Vec<ClassMemberQueryPlan>,
}

struct SourceClassUnionConstructorCandidates {
    value_type: TypeId,
    signatures: Vec<SignatureId>,
    instance_types: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceClassUnionConstructorProvider {
    Ambient(NodeRef),
    ArrayCallback {
        parameter: NodeRef,
        arrow: NodeRef,
        call: NodeRef,
        receiver: NodeRef,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceGlobalObjectConstructorPlan {
    annotation: NodeRef,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    return_annotation: NodeRef,
    parameter: SourceNewParameter,
    object_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceGlobalDateConstructorPlan {
    annotation: NodeRef,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    return_annotation: NodeRef,
}

/// Authenticated zero-argument global Date construction retained by a class parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceGlobalDateInitializerPlan {
    node: NodeRef,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    global: SourceGlobalDateConstructorPlan,
}

impl SourceGlobalDateInitializerPlan {
    pub(super) const fn node(self) -> NodeRef {
        self.node
    }

    pub(super) const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    fn construction(self) -> SourceDefaultNewPlan {
        SourceDefaultNewPlan {
            node: self.node,
            constructor: self.constructor,
            resolved_symbol: self.symbol,
            target: SourceNewTarget::GlobalDate(self.global),
            early_preparation: false,
            type_arguments: Vec::new(),
            argument: None,
            additional_arguments: Vec::new(),
            parameter: None,
            executor: None,
            expression_arguments: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceGlobalPromiseConstructorPlan {
    annotation: NodeRef,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    type_parameter: SemanticSymbolId,
    parameter: SemanticSymbolId,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    executor: NodeRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceGlobalArraySignaturePlan {
    declaration: NodeRef,
    parameter: SemanticSymbolId,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    type_parameter: Option<SemanticSymbolId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceGlobalArraySelection {
    Length,
    GenericLength(TypeId),
    Items(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceGlobalArrayConstructorPlan {
    annotation: NodeRef,
    owner: SemanticSymbolId,
    array_target: TypeId,
    length: SourceGlobalArraySignaturePlan,
    generic_length: SourceGlobalArraySignaturePlan,
    items: SourceGlobalArraySignaturePlan,
    selection: SourceGlobalArraySelection,
}

#[derive(Clone, Debug)]
struct SourceNewArgument {
    node: NodeRef,
    value: SourceNewArgumentValue,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNewTypeArgument {
    node: NodeRef,
    type_: TypeId,
}

#[derive(Clone, Debug)]
enum SourceNewArgumentValue {
    String(String),
    Number(Number),
    Boolean(bool),
    EmptyObject(Box<PropertyObjectPlan>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNewParameter {
    symbol: SemanticSymbolId,
    type_: TypeId,
}

impl SourceDefaultNewPlan {
    pub(super) fn is_library_constructor(&self) -> bool {
        matches!(
            &self.target,
            SourceNewTarget::Library(_) | SourceNewTarget::GenericLibrary(_)
        )
    }

    pub(super) fn expression_argument_nodes(&self) -> Option<&[NodeRef]> {
        self.expression_arguments
            .as_ref()
            .map(|arguments| arguments.nodes.as_slice())
    }

    pub(super) fn checked_expression_arguments(&self) -> Option<&[PlannedExpression]> {
        self.expression_arguments
            .as_ref()
            .and_then(|arguments| arguments.expressions.as_deref())
    }

    pub(super) fn set_expression_arguments(
        &mut self,
        expressions: Vec<PlannedExpression>,
    ) -> Result<(), SourceNewError> {
        let Some(arguments) = &mut self.expression_arguments else {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                self.node,
            )));
        };
        if arguments.expressions.is_some()
            || arguments.nodes.len() != expressions.len()
            || arguments
                .nodes
                .iter()
                .zip(&expressions)
                .any(|(node, expression)| *node != expression.node)
        {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                self.node,
            )));
        }
        arguments.expressions = Some(expressions);
        Ok(())
    }

    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn constructor(&self) -> NodeRef {
        self.constructor
    }

    pub(super) const fn resolved_symbol(&self) -> SemanticSymbolId {
        self.resolved_symbol
    }

    /// Class preparation uses the exported owner, while source reads keep the local symbol.
    pub(super) fn provider_symbol(&self) -> SemanticSymbolId {
        match &self.target {
            SourceNewTarget::Class(class) => class.symbol(),
            SourceNewTarget::SourceClass(class) | SourceNewTarget::ConstructorOverloads(class) => {
                class.symbol()
            }
            SourceNewTarget::GenericSourceClass(generic) => generic.class.symbol(),
            _ => self.resolved_symbol,
        }
    }

    pub(super) fn is_generic_source_class(&self) -> bool {
        matches!(self.target, SourceNewTarget::GenericSourceClass(_))
    }

    pub(super) fn is_generic_library_constructor(&self) -> bool {
        matches!(self.target, SourceNewTarget::GenericLibrary(_))
    }

    pub(super) fn written_type_argument_nodes(&self) -> Option<&[NodeRef]> {
        match &self.target {
            SourceNewTarget::GenericSourceClass(generic) => generic.type_argument_nodes.as_deref(),
            SourceNewTarget::GenericLibrary(generic) => generic.type_argument_nodes.as_deref(),
            _ => None,
        }
    }

    pub(super) const fn requires_early_preparation(&self) -> bool {
        self.early_preparation
    }

    pub(super) fn is_imported_class(&self) -> bool {
        matches!(&self.target, SourceNewTarget::ImportedClass(_))
    }

    pub(super) fn promise_executor_node(&self) -> Option<NodeRef> {
        match &self.target {
            SourceNewTarget::GlobalPromise(global) => Some(global.executor),
            _ => None,
        }
    }

    pub(super) fn set_promise_executor(
        &mut self,
        executor: PlannedExpression,
    ) -> Result<(), SourceNewError> {
        let Some(node) = self.promise_executor_node() else {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                self.constructor,
            )));
        };
        if executor.node != node
            || !matches!(&executor.kind, PlannedExpressionKind::Arrow(_))
            || self.executor.is_some()
        {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                self.constructor,
            )));
        }
        self.executor = Some(Box::new(executor));
        Ok(())
    }

    pub(super) fn promise_executor(&self) -> Option<&PlannedExpression> {
        self.executor.as_deref()
    }

    pub(super) fn promise_executor_contextual_type(
        &self,
        store: &CanonicalTypeMapperStore,
    ) -> Option<TypeId> {
        let SourceNewTarget::GlobalPromise(global) = &self.target else {
            return None;
        };
        store
            .type_node_links(global.parameter_annotation)
            .and_then(|links| links.resolved_type)
    }

    fn arguments(&self) -> impl Iterator<Item = &SourceNewArgument> {
        self.argument.iter().chain(&self.additional_arguments)
    }

    pub(super) fn argument_nodes(&self) -> impl Iterator<Item = NodeRef> + '_ {
        self.arguments().map(|argument| argument.node).chain(
            self.expression_arguments
                .iter()
                .flat_map(|arguments| arguments.nodes.iter().copied()),
        )
    }

    /// Returns the exact access or abstract-instantiation diagnostic for a class.
    pub(super) fn constructor_accessibility_diagnostic(
        &self,
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
    ) -> Result<Option<(u32, String)>, SourceNewError> {
        if let SourceNewTarget::SourceClass(class) = &self.target {
            preflight_direct_default_new(store, host, self)?;
            return Ok(class.is_abstract().then_some((2511, String::new())));
        }
        if let SourceNewTarget::ClassUnion(union) = &self.target {
            return Ok(union
                .classes
                .iter()
                .any(ClassMemberQueryPlan::is_abstract)
                .then_some((2511, String::new())));
        }
        let imported_class;
        let class = match &self.target {
            SourceNewTarget::Class(class) => class.as_ref(),
            SourceNewTarget::ImportedClass(binding) => {
                imported_class = imported_constructor_class(store, host, self, binding)?;
                &imported_class
            }
            _ => return Ok(None),
        };
        let code = match (class.is_abstract(), class.constructor_visibility()) {
            (true, _) => Some(2511),
            (false, ClassConstructorVisibility::Private) => Some(2673),
            (false, ClassConstructorVisibility::Protected) => Some(2674),
            (false, ClassConstructorVisibility::Public) => {
                if !bound
                    .source_facts()
                    .is_some_and(ts_binder::CanonicalSourceFileFacts::is_javascript_file)
                {
                    return Ok(None);
                }
                let Some(constructor) = class.constructor_declaration() else {
                    return Ok(None);
                };
                let comment = leading_jsdoc_comment(arena, constructor)
                    .map_err(|_| invariant(SourceNewInvariant::InvalidClassPlan(constructor)))?;
                let Some(comment) = comment else {
                    return Ok(None);
                };
                let source = arena
                    .source_text()
                    .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(constructor)))?;
                let range = comment.range();
                let start = usize::try_from(range.start.get())
                    .map_err(|_| invariant(SourceNewInvariant::InvalidClassPlan(constructor)))?;
                let end = usize::try_from(range.end.get())
                    .map_err(|_| invariant(SourceNewInvariant::InvalidClassPlan(constructor)))?;
                let comment = source
                    .get(start..end)
                    .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(constructor)))?;
                let mut accessibility = None;
                for (position, _) in comment.match_indices('@') {
                    if position < 3
                        || position + 1 >= comment.len().saturating_sub(2)
                        || comment
                            .get(..position)
                            .and_then(|prefix| prefix.chars().next_back())
                            .is_none_or(|character| !character.is_whitespace())
                    {
                        continue;
                    }
                    let name = comment[position + 1..]
                        .split(|character: char| {
                            !character.is_alphanumeric() && !matches!(character, '_' | '$' | '-')
                        })
                        .next()
                        .unwrap_or_default();
                    let code = match name {
                        "private" => 2673,
                        "protected" => 2674,
                        _ => continue,
                    };
                    if accessibility.replace(code).is_some() {
                        return Err(invariant(SourceNewInvariant::InvalidClassPlan(constructor)));
                    }
                }
                accessibility
            }
        };
        let Some(code) = code else {
            return Ok(None);
        };
        let symbol = store
            .symbol(class.symbol())
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(class.symbol())))?;
        let name = if symbol.name() == InternalSymbolName::Default.as_ref() {
            let declaration = host.node(class.declaration()).ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()))
            })?;
            let NodeData::ClassDeclaration(declaration) = &declaration.data else {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                    class.declaration(),
                )));
            };
            let name = declaration.name.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()))
            })?;
            let name = NodeRef::new(class.declaration().arena, class.declaration().file, name);
            let Some(NodeData::Identifier(identifier)) = host.node(name).map(|node| &node.data)
            else {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(name)));
            };
            identifier.text.as_str()
        } else {
            symbol
                .name()
                .as_utf8()
                .filter(|name| !name.is_empty())
                .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(class.symbol())))?
        };
        Ok(Some((code, name.to_owned())))
    }
}

/// Recognizes the JavaScript Promise executor call that owns diagnostic TS2810.
pub(super) fn promise_executor_missing_argument_is_exact(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    call: NodeRef,
    callee: NodeRef,
    signature: SignatureId,
) -> bool {
    let Some(call_record) = host.node(call) else {
        return false;
    };
    let NodeData::CallExpression(expression) = &call_record.data else {
        return false;
    };
    let Some(arrow) = call_record
        .parent
        .map(|node| NodeRef::new(call.arena, call.file, node))
    else {
        return false;
    };
    let Some(arrow_record) = host.node(arrow) else {
        return false;
    };
    let NodeData::ArrowFunction(executor) = &arrow_record.data else {
        return false;
    };
    let [parameter] = executor.parameters.nodes.as_slice() else {
        return false;
    };
    let parameter = NodeRef::new(arrow.arena, arrow.file, *parameter);
    let Some(bound) = host.bound_file(arrow) else {
        return false;
    };
    let Some(parameter_symbol) = bound
        .symbol(parameter)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(callee_record) = host.node(callee) else {
        return false;
    };
    let NodeData::Identifier(identifier) = &callee_record.data else {
        return false;
    };
    let Some(annotation) = store.signature(signature).and_then(Signature::declaration) else {
        return false;
    };
    let Some(resolve_parameter) = host
        .node(annotation)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return false;
    };
    let Some(executor_annotation) = host
        .node(resolve_parameter)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return false;
    };
    let Some(constructor_parameter) = host
        .node(executor_annotation)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return false;
    };
    let Some(constructor_declaration) = host
        .node(constructor_parameter)
        .and_then(|record| record.parent)
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return false;
    };
    let Some(owner) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("PromiseConstructor"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };

    call_record.kind == SyntaxKind::CallExpression
        && call_record.flags.0 == 0
        && expression.expression == callee.node
        && expression.arguments.nodes.is_empty()
        && arrow_record.kind == SyntaxKind::ArrowFunction
        && executor.body == call.node
        && bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_javascript_file)
        && source_promise_constructor_argument_arrow_is_exact(store, host, arrow)
            .is_ok_and(|valid| valid)
        && callee_record.kind == SyntaxKind::Identifier
        && callee_record.parent == Some(call.node)
        && identifier.text == "resolve"
        && bound
            .locals(arrow)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            == Some(parameter_symbol)
        && store.symbol(parameter_symbol).is_some_and(|symbol| {
            symbol.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                && symbol.check_flags() == CheckFlags::NONE
                && symbol.name().as_utf8() == Some(identifier.text.as_str())
                && symbol.declarations() == Some(&[parameter])
                && symbol.value_declaration() == Some(parameter)
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.parent().is_none()
                && symbol.export_symbol().is_none()
        })
        && store.symbol_node_links(callee).is_none_or(|links| {
            links
                .resolved_symbol
                .is_none_or(|symbol| symbol == parameter_symbol)
        })
        && host.node(annotation).map(|record| record.kind) == Some(SyntaxKind::FunctionType)
        && host.node(resolve_parameter).map(|record| record.kind) == Some(SyntaxKind::Parameter)
        && host.node(executor_annotation).map(|record| record.kind)
            == Some(SyntaxKind::FunctionType)
        && host.node(constructor_parameter).map(|record| record.kind) == Some(SyntaxKind::Parameter)
        && host.node(constructor_declaration).map(|record| record.kind)
            == Some(SyntaxKind::ConstructSignature)
        && store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
            .and_then(|constructor| store.symbol(constructor))
            .and_then(|constructor| constructor.declarations())
            .is_some_and(|declarations| declarations.contains(&constructor_declaration))
}

/// Exact selected signature and result of one default construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceDefaultNew {
    pub(super) value_type: TypeId,
    pub(super) instance_type: TypeId,
    pub(super) signature: SignatureId,
}

/// Proves direct-new syntax and its preceding class or ambient constructor.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_direct_default_new(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    prior_source_classes: &HashMap<SemanticSymbolId, SourceClassPlan>,
    import_bindings: &HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    node: NodeRef,
    early_preparation: bool,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    plan_direct_default_new_with_type_context(
        arena,
        bound,
        store,
        host,
        prior_classes,
        prior_source_classes,
        import_bindings,
        node,
        early_preparation,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_direct_default_new_with_type_context(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    prior_source_classes: &HashMap<SemanticSymbolId, SourceClassPlan>,
    import_bindings: &HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    node: NodeRef,
    early_preparation: bool,
    type_context: Option<&super::classes::ClassTypeQueryContext>,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    plan_direct_default_new_with_context(
        arena,
        bound,
        store,
        host,
        prior_classes,
        prior_source_classes,
        import_bindings,
        node,
        early_preparation,
        type_context,
        None,
    )
}

/// Uses the current source caller to admit a real default-library value.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_direct_default_new_with_source_context(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    prior_source_classes: &HashMap<SemanticSymbolId, SourceClassPlan>,
    import_bindings: &HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    node: NodeRef,
    early_preparation: bool,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    let type_context = super::classes::ClassTypeQueryContext::new(globals, options);
    plan_direct_default_new_with_context(
        arena,
        bound,
        store,
        host,
        prior_classes,
        prior_source_classes,
        import_bindings,
        node,
        early_preparation,
        Some(&type_context),
        Some((globals, options)),
    )
}

#[allow(clippy::too_many_arguments)]
fn plan_direct_default_new_with_context(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    prior_source_classes: &HashMap<SemanticSymbolId, SourceClassPlan>,
    import_bindings: &HashMap<SemanticSymbolId, SourceImportBindingPlan>,
    node: NodeRef,
    early_preparation: bool,
    type_context: Option<&super::classes::ClassTypeQueryContext>,
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    let record = arena
        .get(node.node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    let NodeData::NewExpression(new_expression) = &record.data else {
        return Err(unsupported(SourceNewUnsupported::Expression(node)));
    };
    if record.kind != SyntaxKind::NewExpression || record.flags.0 != 0 || new_expression.facts != 0
    {
        return Err(unsupported(SourceNewUnsupported::Expression(node)));
    }
    let mut arguments = Vec::new();
    let mut executor = None;
    let mut has_expression_arguments = false;
    let argument_start = match new_expression.arguments.as_ref() {
        Some(argument_nodes) => {
            if argument_nodes.range.start < record.range.start
                || argument_nodes.range.end != record.range.end
                || argument_nodes.range.end.get()
                    < argument_nodes.range.start.get().saturating_add(2)
                || arena.source_text().is_some_and(|source| {
                    let open = usize::try_from(argument_nodes.range.start.get()).ok();
                    let close =
                        usize::try_from(argument_nodes.range.end.get().saturating_sub(1)).ok();
                    open.is_none_or(|open| source.as_bytes().get(open) != Some(&b'('))
                        || close.is_none_or(|close| source.as_bytes().get(close) != Some(&b')'))
                })
            {
                return Err(unsupported(SourceNewUnsupported::Arguments(node)));
            }
            for &argument_node in &argument_nodes.nodes {
                let argument_node = NodeRef::new(node.arena, node.file, argument_node);
                let argument_record = arena
                    .get(argument_node.node)
                    .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(argument_node)))?;
                if matches!(&argument_record.data, NodeData::ArrowFunction(_))
                    && argument_record.kind == SyntaxKind::ArrowFunction
                {
                    if argument_nodes.nodes.len() != 1
                        || executor.replace(argument_node).is_some()
                        || argument_record.flags.0 != 0
                        || argument_record.parent != Some(node.node)
                        || argument_record.range.start <= argument_nodes.range.start
                        || argument_record.range.end >= argument_nodes.range.end
                        || !bound.contains(argument_node)
                    {
                        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                    }
                    continue;
                }
                if argument_record.flags.0 != 0
                    || argument_record.parent != Some(node.node)
                    || argument_record.range.start <= argument_nodes.range.start
                    || argument_record.range.end >= argument_nodes.range.end
                    || !bound.contains(argument_node)
                    || matches!(
                        argument_record.kind,
                        SyntaxKind::SpreadElement | SyntaxKind::OmittedExpression
                    )
                {
                    return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                }
                let value = match &argument_record.data {
                    NodeData::StringLiteral(literal)
                        if argument_record.kind == SyntaxKind::StringLiteral
                            && literal.token_flags.0 == 0 =>
                    {
                        SourceNewArgumentValue::String(literal.text.clone())
                    }
                    NodeData::NumericLiteral(literal)
                        if argument_record.kind == SyntaxKind::NumericLiteral
                            && literal.token_flags.0 == 0 =>
                    {
                        let value = ts_jsnum::from_string(&literal.text);
                        let spelling_valid = arena.source_text().is_none_or(|source| {
                            let start = usize::try_from(argument_record.range.start.get()).ok();
                            let end = usize::try_from(argument_record.range.end.get()).ok();
                            start
                                .zip(end)
                                .and_then(|(start, end)| source.get(start..end))
                                .and_then(normalize_numeric_separators)
                                .is_some_and(|spelling| {
                                    let source_value = ts_jsnum::from_string(&spelling);
                                    !source_value.is_nan() && source_value == value
                                })
                        });
                        if value.is_nan() || !spelling_valid {
                            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                        }
                        SourceNewArgumentValue::Number(value)
                    }
                    NodeData::KeywordExpression(keyword)
                        if matches!(
                            argument_record.kind,
                            SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword
                        ) && keyword.flow_node.is_none() =>
                    {
                        SourceNewArgumentValue::Boolean(
                            argument_record.kind == SyntaxKind::TrueKeyword,
                        )
                    }
                    NodeData::ObjectLiteralExpression(object)
                        if argument_record.kind == SyntaxKind::ObjectLiteralExpression
                            && object.properties.nodes.is_empty()
                            && object.symbol.is_none()
                            && object.facts == 0 =>
                    {
                        let planned = plan_object_literal(store, host, argument_node)
                            .map_err(|_| unsupported(SourceNewUnsupported::Arguments(node)))?;
                        if !planned.properties.is_empty()
                            || !planned.methods.is_empty()
                            || !planned.accessors.is_empty()
                            || !planned.spreads.is_empty()
                            || !planned.indexes.is_empty()
                            || !planned.call_signatures.is_empty()
                        {
                            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                        }
                        SourceNewArgumentValue::EmptyObject(Box::new(planned))
                    }
                    _ => {
                        has_expression_arguments = true;
                        continue;
                    }
                };
                if argument_record.flags.0 != 0
                    || argument_record.parent != Some(node.node)
                    || argument_record.range.start <= argument_nodes.range.start
                    || argument_record.range.end >= argument_nodes.range.end
                    || !bound.contains(argument_node)
                {
                    return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                }
                arguments.push(SourceNewArgument {
                    node: argument_node,
                    value,
                });
            }
            argument_nodes.range.start
        }
        None => record.range.end,
    };

    let constructor = NodeRef::new(node.arena, node.file, new_expression.expression);
    let constructor_record = arena
        .get(constructor.node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(constructor)))?;
    let NodeData::Identifier(identifier) = &constructor_record.data else {
        return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
    };
    if constructor_record.kind != SyntaxKind::Identifier
        || constructor_record.flags.0 != 0
        || constructor_record.parent != Some(node.node)
        || constructor_record.range.start < record.range.start
        || constructor_record.range.end > argument_start
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
    }
    if new_expression.arguments.is_none() && constructor_record.range.end != record.range.end {
        return Err(unsupported(SourceNewUnsupported::MissingArgumentList(node)));
    }

    let mut callback_host = host.name_resolver_host(store)?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| {
                invariant(SourceNewInvariant::NameResolution {
                    node: constructor,
                    error,
                })
            })?;
    let resolved_symbol = match resolver.resolve(
        Some(CanonicalResolutionLocation::Bound(constructor)),
        &identifier.text,
        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
        None,
        false,
        false,
    ) {
        Ok(Some(symbol)) => symbol,
        Err(CanonicalNameResolutionError::AliasResolutionUnavailable(symbol))
            if import_bindings.contains_key(&symbol) =>
        {
            symbol
        }
        Ok(None) | Err(CanonicalNameResolutionError::AliasResolutionUnavailable(_)) => {
            return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
        }
        Err(error) => {
            return Err(invariant(SourceNewInvariant::NameResolution {
                node: constructor,
                error,
            }));
        }
    };
    let symbol = constructor_value_symbol(store, constructor, resolved_symbol)?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(symbol)))?;
    if let Some(class) = prior_source_classes.get(&symbol).filter(|class| {
        symbol_record.flags() == SymbolFlags::CLASS && !class.type_parameters().is_empty()
    }) {
        return plan_generic_source_class_new(
            store,
            host,
            node,
            constructor,
            resolved_symbol,
            class,
            early_preparation,
        );
    }
    let mut library = source_context
        .map(|(globals, options)| {
            plan_global_constructor_value(store, host, globals, options, symbol)
                .map_err(|error| {
                    trace_constructor_failure(
                        "provider_plan_literal",
                        node,
                        constructor,
                        format_args!("provider={symbol:?} raw_error={error:?}"),
                    );
                    global_error::provider_error(constructor, symbol, error)
                })
        })
        .transpose()?
        .flatten();
    let source_arguments = symbol_record.flags() == SymbolFlags::CLASS
        && prior_source_classes
            .get(&symbol)
            .is_some_and(SourceClassPlan::has_checked_constructor_arguments);
    let expression_argument_plan = || SourceNewExpressionArguments {
        nodes: new_expression
            .arguments
            .as_ref()
            .map_or_else(Vec::new, |arguments| {
                arguments
                    .nodes
                    .iter()
                    .map(|&argument| NodeRef::new(node.arena, node.file, argument))
                    .collect()
            }),
        expressions: None,
    };
    let mut expression_arguments =
        (source_arguments || library.is_some()).then(expression_argument_plan);
    if source_arguments || library.is_some() {
        if library.is_some() && executor.is_some() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        arguments.clear();
        executor = None;
        if new_expression.type_arguments.is_some() {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
        }
    }
    let global_wrapper = !source_arguments
        && matches!(identifier.text.as_str(), "Object" | "Boolean")
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source(&identifier.text))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    let global_array = !source_arguments
        && identifier.text == "Array"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    let global_date = !source_arguments
        && identifier.text == "Date"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Date"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    let imported_class = import_bindings.contains_key(&resolved_symbol);
    let global_promise = !source_arguments
        && identifier.text == "Promise"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Promise"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    if !(source_arguments
        || library.is_some()
        || global_wrapper
        || global_array
        || global_date
        || global_promise)
        && let Some((globals, options)) = source_context
        && let Some(named) = plan_global_named_constructor(store, host, globals, options, symbol)
            .and_then(|named| match named {
                Some(named) => Ok(Some(named)),
                None => {
                    plan_source_generic_constructor_value(store, host, globals, options, symbol)
                }
            })
            .map_err(|error| {
                trace_constructor_failure(
                    "provider_plan_named",
                    node,
                    constructor,
                    format_args!("provider={symbol:?} raw_error={error:?}"),
                );
                global_error::provider_error(constructor, symbol, error)
            })?
    {
        if named.is_named_generic() {
            return plan_generic_library_new(
                store,
                host,
                globals,
                options,
                node,
                constructor,
                resolved_symbol,
                named,
                early_preparation,
            );
        }
        expression_arguments = Some(expression_argument_plan());
        if executor.is_some() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        arguments.clear();
        executor = None;
        if new_expression.type_arguments.is_some() {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
        }
        library = Some(named);
    }
    if has_expression_arguments && !(source_arguments || library.is_some()) {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }
    if executor.is_some() && !global_promise {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }
    if !(global_array || global_wrapper && identifier.text == "Boolean")
        && arguments
            .iter()
            .any(|argument| matches!(&argument.value, SourceNewArgumentValue::EmptyObject(_)))
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }
    if !global_array
        && (arguments.len() > 1 || new_expression.type_arguments.is_some() && !imported_class)
    {
        return Err(unsupported(if new_expression.type_arguments.is_some() {
            SourceNewUnsupported::TypeArguments(node)
        } else {
            SourceNewUnsupported::Arguments(node)
        }));
    }
    let type_arguments = if imported_class {
        plan_imported_class_type_arguments(arena, bound, store, node)?
    } else {
        Vec::new()
    };
    let argument = arguments.first().cloned();
    let additional_arguments = arguments.into_iter().skip(1).collect::<Vec<_>>();
    let (target, parameter) = if let Some(library) = library {
        (SourceNewTarget::Library(Box::new(library)), None)
    } else if let Some(binding) = import_bindings.get(&resolved_symbol) {
        if symbol_record.flags() != SymbolFlags::ALIAS
            || binding.alias_symbol != resolved_symbol
            || binding.local_text != identifier.text
            || binding.declaration.file != node.file
        {
            return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
        }
        (
            SourceNewTarget::ImportedClass(Box::new(binding.clone())),
            None,
        )
    } else if global_wrapper {
        let global = plan_global_object_constructor(store, host, constructor, symbol)?;
        (
            SourceNewTarget::GlobalObject(global),
            argument.as_ref().map(|_| global.parameter),
        )
    } else if global_array {
        let global = plan_global_array_constructor(
            arena,
            store,
            host,
            node,
            constructor,
            symbol,
            argument.as_ref(),
            &additional_arguments,
        )?;
        let number = store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.number_type)
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidConstructorCache(constructor)))?;
        let parameter = argument.as_ref().map(|_| SourceNewParameter {
            symbol: match global.selection {
                SourceGlobalArraySelection::Length => global.length.parameter,
                SourceGlobalArraySelection::GenericLength(_) => global.generic_length.parameter,
                SourceGlobalArraySelection::Items(_) => global.items.parameter,
            },
            type_: match global.selection {
                SourceGlobalArraySelection::Length
                | SourceGlobalArraySelection::GenericLength(_) => number,
                SourceGlobalArraySelection::Items(element) => element,
            },
        });
        (SourceNewTarget::GlobalArray(global), parameter)
    } else if global_date {
        if argument.is_some() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        let global = plan_global_date_constructor(store, host, constructor, symbol)?;
        (SourceNewTarget::GlobalDate(global), None)
    } else if global_promise {
        let Some(executor) = executor else {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        };
        if argument.is_some()
            || !source_promise_constructor_argument_arrow_is_exact(store, host, executor)
                .map_err(|_| unsupported(SourceNewUnsupported::Arguments(node)))?
        {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        let global = plan_global_promise_constructor(store, host, constructor, symbol, executor)?;
        (SourceNewTarget::GlobalPromise(global), None)
    } else if symbol_record.flags() == SymbolFlags::CLASS
        && let Some(class) = super::classes::plan_source_constructor_overload_class(
            store,
            host,
            symbol,
            type_context,
        )?
    {
        let declaration = class.declaration();
        if !declaration.is_for(node.arena, node.file)
            || host
                .node(declaration)
                .is_none_or(|declaration| declaration.range.end > record.range.start)
        {
            return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                node: constructor,
                symbol,
            }));
        }
        (SourceNewTarget::ConstructorOverloads(Box::new(class)), None)
    } else if let Some(class) = prior_source_classes.get(&symbol).filter(|class| {
        symbol_record.flags() == SymbolFlags::CLASS
            && (!class.has_object_base() || class.has_constructor_value_base())
    }) {
        if !(class.has_own_default_constructor() || source_arguments) || early_preparation {
            return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
        }
        if argument.is_some() || !additional_arguments.is_empty() || !type_arguments.is_empty() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        (SourceNewTarget::SourceClass(Box::new(class.clone())), None)
    } else if symbol_record.flags() == SymbolFlags::CLASS {
        let class = if let Some(class) = prior_classes.get(&symbol) {
            ClassMemberQueryPlan::Direct(class.clone())
        } else {
            let class = plan_nongeneric_class_member_query(store, host, symbol)?;
            let ClassMemberQueryPlan::Derived {
                class: derived,
                base,
            } = &class
            else {
                return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                    node: constructor,
                    symbol,
                }));
            };
            let declaration = derived.declaration();
            if !declaration.is_for(node.arena, node.file) {
                return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                    node: constructor,
                    symbol,
                }));
            }
            let declaration_record = arena
                .get(declaration.node)
                .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(declaration)))?;
            if declaration_record.range.end > record.range.start
                || prior_classes.get(&base.symbol()) != Some(base.as_ref())
            {
                return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                    node: constructor,
                    symbol,
                }));
            }
            class
        };
        if class.symbol() != symbol {
            return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                class.declaration(),
            )));
        }
        preflight_nongeneric_class_member_query(store, host, &class)?;
        if class.constructor_interface_annotation().is_some() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        if class.constructor_annotation().is_some()
            && (argument.is_some() || class.constructor_minimum_argument_count() != 0)
        {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        let parameter = constructor_parameter(store, host, &class)?;
        if argument.is_some() && class.direct_plan().is_none() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        (SourceNewTarget::Class(Box::new(class)), parameter)
    } else if global_error::is_named_interface_value(store, host, symbol) {
        let declared = global_error::plan(store, host, constructor, symbol, argument.as_ref())?;
        let parameter = declared.parameter;
        (SourceNewTarget::DeclaredInterface(declared), parameter)
    } else if matches!(
        symbol_record.flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
    ) {
        let callback = if argument.is_none() {
            plan_callback_class_union_constructor(
                arena,
                bound,
                store,
                host,
                prior_classes,
                node,
                constructor,
                symbol,
            )?
        } else {
            None
        };
        if let Some(union) = callback {
            (SourceNewTarget::ClassUnion(union), None)
        } else {
            let declared = plan_declared_constructor(
                arena,
                bound,
                store,
                host,
                node,
                constructor,
                symbol,
                argument.as_ref(),
            );
            match declared {
                Ok(declared) => (SourceNewTarget::Declared(declared), declared.parameter),
                Err(SourceNewError::Unsupported(SourceNewUnsupported::ConstructorClass {
                    ..
                })) if argument.is_none() => {
                    let union = plan_declared_class_union_constructor(
                        arena,
                        bound,
                        store,
                        host,
                        prior_classes,
                        node,
                        constructor,
                        symbol,
                    )?;
                    (SourceNewTarget::ClassUnion(union), None)
                }
                Err(error) => return Err(error),
            }
        }
    } else {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }));
    };
    let omitted_defaulted_class_parameter = argument.is_none()
        && parameter.is_some()
        && matches!(
            &target,
            SourceNewTarget::Class(class) if class.constructor_minimum_argument_count() == 0
        );
    let checked_class_arguments = source_context.is_some()
        && !early_preparation
        && parameter.is_some()
        && additional_arguments.is_empty()
        && argument.as_ref().is_some_and(|argument| {
            matches!(
                &argument.value,
                SourceNewArgumentValue::String(_)
                    | SourceNewArgumentValue::Number(_)
                    | SourceNewArgumentValue::Boolean(_)
            )
        })
        && matches!(
            &target,
            SourceNewTarget::Class(class)
                if class.direct_plan().is_some()
                    && !class.is_abstract()
                    && class.constructor_visibility() == ClassConstructorVisibility::Public
        );
    if !checked_class_arguments
        && !matches!(
            &target,
            SourceNewTarget::ImportedClass(_)
                | SourceNewTarget::ConstructorOverloads(_)
                | SourceNewTarget::SourceClass(_)
        )
        && (argument.is_some() != parameter.is_some() && !omitted_defaulted_class_parameter
            || argument
                .as_ref()
                .zip(parameter)
                .is_some_and(|(argument, parameter)| {
                    !argument_matches_parameter(store, argument, parameter)
                }))
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }

    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        target,
        early_preparation,
        type_arguments,
        argument: if checked_class_arguments {
            None
        } else {
            argument
        },
        additional_arguments,
        parameter,
        executor: None,
        expression_arguments: if checked_class_arguments {
            Some(expression_argument_plan())
        } else {
            expression_arguments
        },
    };
    preflight_default_new_cache_with_context(store, host, &plan, source_context)?;
    Ok(plan)
}

fn generic_source_class_type_argument_nodes(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    constructor: NodeRef,
) -> Result<Option<Vec<NodeRef>>, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(node));
    let (arena, bound) = host.source(node).ok_or_else(invalid)?;
    let record = host.node(node).ok_or_else(invalid)?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Err(invalid());
    };
    let Some(arguments) = &expression.type_arguments else {
        return Ok(None);
    };
    let constructor_end = host.node(constructor).ok_or_else(invalid)?.range.end;
    let argument_start = expression
        .arguments
        .as_ref()
        .map_or(record.range.end, |arguments| arguments.range.start);
    if arguments.range.start < constructor_end
        || arguments.range.end > argument_start
        || arguments.range.end < arguments.range.start
    {
        return Err(invalid());
    }
    let mut previous_end = arguments.range.start;
    let mut nodes = Vec::with_capacity(arguments.nodes.len());
    for &child in &arguments.nodes {
        let child = NodeRef::new(node.arena, node.file, child);
        let child_record = arena.get(child.node).ok_or_else(invalid)?;
        if child_record.parent != Some(node.node)
            || child_record.flags.0 != 0
            || child_record.range.start < previous_end
            || child_record.range.end > arguments.range.end
            || !bound.contains(child)
            || nodes.contains(&child)
        {
            return Err(invalid());
        }
        previous_end = child_record.range.end;
        nodes.push(child);
    }
    Ok(Some(nodes))
}

fn plan_generic_source_class_new(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    class: &SourceClassPlan,
    early_preparation: bool,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    if !class.has_generic_constructor() || early_preparation {
        return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
    }
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()));
    let declaration = host.node(class.declaration()).ok_or_else(invalid)?;
    let record = host.node(node).ok_or_else(invalid)?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Err(invalid());
    };
    if !class.declaration().is_for(node.arena, node.file)
        || declaration.range.end > record.range.start
    {
        return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
            node: constructor,
            symbol: class.symbol(),
        }));
    }
    let type_argument_nodes = generic_source_class_type_argument_nodes(host, node, constructor)?;
    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        target: SourceNewTarget::GenericSourceClass(SourceGenericClassNewPlan {
            class: Box::new(class.clone()),
            type_argument_nodes,
        }),
        early_preparation,
        type_arguments: Vec::new(),
        argument: None,
        additional_arguments: Vec::new(),
        parameter: None,
        executor: None,
        expression_arguments: Some(SourceNewExpressionArguments {
            nodes: expression
                .arguments
                .as_ref()
                .map_or_else(Vec::new, |arguments| {
                    arguments
                        .nodes
                        .iter()
                        .map(|&argument| NodeRef::new(node.arena, node.file, argument))
                        .collect()
                }),
            expressions: None,
        }),
    };
    preflight_direct_default_new(store, host, &plan)?;
    Ok(plan)
}

/// Keeps written type arguments and checked value arguments on the named owner.
#[allow(clippy::too_many_arguments)]
fn plan_generic_library_new(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    node: NodeRef,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    library: GlobalConstructorValuePlan,
    early_preparation: bool,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    let type_argument_nodes = generic_source_class_type_argument_nodes(host, node, constructor)?;
    let Some(NodeData::NewExpression(expression)) = host.node(node).map(|record| &record.data)
    else {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(node)));
    };
    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        target: SourceNewTarget::GenericLibrary(SourceGenericLibraryNewPlan {
            library: Box::new(library),
            type_argument_nodes,
        }),
        early_preparation,
        type_arguments: Vec::new(),
        argument: None,
        additional_arguments: Vec::new(),
        parameter: None,
        executor: None,
        expression_arguments: Some(SourceNewExpressionArguments {
            nodes: expression
                .arguments
                .as_ref()
                .map_or_else(Vec::new, |arguments| {
                    arguments
                        .nodes
                        .iter()
                        .map(|&argument| NodeRef::new(node.arena, node.file, argument))
                        .collect()
                }),
            expressions: None,
        }),
    };
    preflight_direct_default_new_with_source_context(store, host, globals, options, &plan)?;
    Ok(plan)
}

/// Follows an exported local value without changing its lexical symbol identity.
fn constructor_value_symbol(
    store: &CanonicalTypeMapperStore,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
) -> Result<SemanticSymbolId, SourceNewError> {
    let symbol = store
        .get_merged_symbol(resolved_symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(resolved_symbol)))?;
    if symbol != resolved_symbol {
        return Err(invariant(SourceNewInvariant::MergedSymbol {
            source: resolved_symbol,
            target: symbol,
        }));
    }
    let record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(symbol)))?;
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    if record.check_flags() != CheckFlags::NONE {
        return Err(reject());
    }
    if record.flags() != SymbolFlags::EXPORT_VALUE {
        return Ok(symbol);
    }
    let target = record.export_symbol().ok_or_else(reject)?;
    let exported = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(target)))?;
    if exported.flags() != SymbolFlags::CLASS
        || exported.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(target) != Some(target)
    {
        return Err(reject());
    }
    Ok(target)
}

/// Retains the normal global Date constructor proof without publishing its cold type.
pub(super) fn plan_global_date_initializer(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<SourceGlobalDateInitializerPlan, SourceNewError> {
    let (arena, bound) = host
        .source(node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    let plan = plan_direct_default_new(
        arena,
        bound,
        store,
        host,
        &HashMap::new(),
        &HashMap::new(),
        &HashMap::new(),
        node,
        false,
    )?;
    let SourceNewTarget::GlobalDate(global) = plan.target else {
        return Err(unsupported(SourceNewUnsupported::Constructor(
            plan.constructor,
        )));
    };
    Ok(SourceGlobalDateInitializerPlan {
        node,
        constructor: plan.constructor,
        symbol: plan.resolved_symbol,
        global,
    })
}

/// Publishes an authenticated Date default before its owning class can publish.
pub(super) fn materialize_global_date_initializer(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    initializer: SourceGlobalDateInitializerPlan,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    let plan = initializer.construction();
    preflight_direct_default_new(store, host, &plan)?;
    materialize_global_date_constructor(store, host, &plan, &initializer.global)?;

    let missing_types = usize::from(store.type_node_links(plan.constructor).is_none())
        + usize::from(store.type_node_links(plan.node).is_none());
    if !store.try_reserve_symbol_node_links(usize::from(
        store.symbol_node_links(plan.constructor).is_none(),
    )) || !store.try_reserve_type_node_links(missing_types)
        || !store
            .try_reserve_signature_links(usize::from(store.signature_links(plan.node).is_none()))
    {
        return Err(invariant(SourceNewInvariant::Capacity(plan.node)));
    }
    if store.symbol_node_links(plan.constructor).is_none() {
        assert!(store.ensure_symbol_node_links(plan.constructor));
    }
    if store.type_node_links(plan.constructor).is_none() {
        assert!(store.ensure_type_node_links(plan.constructor));
    }
    if store.signature_links(plan.node).is_none() {
        assert!(store.ensure_signature_links(plan.node));
    }
    if store.type_node_links(plan.node).is_none() {
        assert!(store.ensure_type_node_links(plan.node));
    }
    check_direct_default_new(store, host, &plan)
}

/// Validates the completed global Date expression using only stored source provenance.
pub(super) fn exact_global_date_initializer(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    expected_type: TypeId,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let Some(globals) = store.symbol_table(bootstrap.globals) else {
        return false;
    };
    let Some(symbol) = globals
        .get_source("Date")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(owner) = globals
        .get_source("DateConstructor")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(constructor_index) = node
        .node
        .index()
        .checked_sub(1)
        .and_then(|index| u32::try_from(index).ok())
    else {
        return false;
    };
    let constructor = NodeRef::new(
        node.arena,
        node.file,
        ts_ast::NodeId::new(constructor_index),
    );
    let Some(value_type) = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
    else {
        return false;
    };
    let Some(signature) = store
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
    else {
        return false;
    };
    let Some(signature_record) = store.signature(signature) else {
        return false;
    };
    let Some(declaration) = signature_record.declaration() else {
        return false;
    };
    let Some(constructor_signature) = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|signature| store.get_merged_symbol(signature))
    else {
        return false;
    };
    let Some((return_annotation, false)) = store.function_signature_return_annotation(signature)
    else {
        return false;
    };
    store.source_node_kind(node) == Some(SyntaxKind::NewExpression)
        && store.source_node_kind(constructor) == Some(SyntaxKind::Identifier)
        && store.source_identifier_text(constructor) == Some("Date")
        && store.source_node_parent(constructor)
            == Some(super::store::SourceNodeParent::Parent(node))
        && store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            == Some(expected_type)
        && store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            == Some(value_type)
        && store
            .symbol(constructor_signature)
            .and_then(|symbol| symbol.declarations())
            .is_some_and(|declarations| declarations.contains(&declaration))
        && store.signature_links(declaration)
            == Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        && store.type_node_links(return_annotation)
            == Some(&TypeNodeLinks {
                resolved_type: Some(expected_type),
                ..TypeNodeLinks::default()
            })
        && store.symbol_node_links(constructor)
            == Some(&SymbolNodeLinks {
                resolved_symbol: Some(symbol),
            })
        && store.type_node_links(constructor)
            == Some(&TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            })
        && store.type_node_links(node)
            == Some(&TypeNodeLinks {
                resolved_type: Some(expected_type),
                ..TypeNodeLinks::default()
            })
        && store.signature_links(node)
            == Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        && signature_record.flags() == SignatureFlags::CONSTRUCT
        && signature_record.parameters().is_empty()
        && signature_record.min_argument_count() == 0
        && signature_record.resolved_return_type() == Some(expected_type)
        && authenticated_global_date_constructor_return(store, signature) == Some(expected_type)
}

fn plan_imported_class_type_arguments(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Vec<SourceNewTypeArgument>, SourceNewError> {
    let record = arena
        .get(node.node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Err(unsupported(SourceNewUnsupported::Expression(node)));
    };
    let Some(arguments) = expression.type_arguments.as_ref() else {
        return Ok(Vec::new());
    };
    if arguments.nodes.is_empty() || arguments.has_trailing_comma {
        return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidExpressionCache(node)))?;
    let mut planned = Vec::new();
    planned
        .try_reserve_exact(arguments.nodes.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(node)))?;
    for argument in &arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let record = arena
            .get(argument.node)
            .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(argument)))?;
        if record.parent != Some(node.node)
            || record.flags.0 != 0
            || !bound.contains(argument)
            || !matches!(record.data, NodeData::KeywordTypeNode(_))
        {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(argument)));
        }
        let type_ = match record.kind {
            SyntaxKind::StringKeyword => bootstrap.string_type,
            SyntaxKind::NumberKeyword => bootstrap.number_type,
            SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
            SyntaxKind::AnyKeyword => bootstrap.any_type,
            SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
            _ => return Err(unsupported(SourceNewUnsupported::TypeArguments(argument))),
        };
        if exact_type_cache(store, argument)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument)))?
            .is_some_and(|cached| cached != type_)
        {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument,
            )));
        }
        planned.push(SourceNewTypeArgument {
            node: argument,
            type_,
        });
    }
    Ok(planned)
}

fn plan_global_object_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<SourceGlobalObjectConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(reject)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(reject)?;
    let object = store.symbol(symbol).ok_or_else(reject)?;
    let allowed_object_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let object_type = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .ok_or_else(reject)?;
    let object_record = store.type_payload(object_type).ok_or_else(reject)?;
    let declaration = object.value_declaration().ok_or_else(reject)?;
    let (arena, bound) = host.source(declaration).ok_or_else(reject)?;
    let declaration_record = arena.get(declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(reject)?;
    let annotation_record = arena.get(annotation.node).ok_or_else(reject)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(reject());
    };
    let annotation_name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let annotation_name_record = arena.get(annotation_name.node).ok_or_else(reject)?;
    let NodeData::Identifier(annotation_identifier) = &annotation_name_record.data else {
        return Err(reject());
    };
    let (instance_name, constructor_name) = match object.name().as_utf8() {
        Some("Object") => ("Object", "ObjectConstructor"),
        Some("Boolean") => ("Boolean", "BooleanConstructor"),
        _ => return Err(reject()),
    };
    let owner = globals
        .get_source(constructor_name)
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or_else(reject)?;
    let owner_record = store.symbol(owner).ok_or_else(reject)?;
    let owner_declarations = owner_record.declarations().ok_or_else(reject)?;
    let signature_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|signature| store.get_merged_symbol(signature))
        .ok_or_else(reject)?;
    let signature_record = store.symbol(signature_symbol).ok_or_else(reject)?;
    let signature_declarations = signature_record.declarations().ok_or_else(reject)?;
    if object.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || !object
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || object.flags().without(allowed_object_flags) != SymbolFlags::NONE
        || object.check_flags() != CheckFlags::NONE
        || object.name().as_utf8() != Some(instance_name)
        || object.parent().is_some()
        || object.exports().is_some()
        || object.export_symbol().is_some()
        || globals
            .get_source(instance_name)
            .and_then(|global| store.get_merged_symbol(global))
            != Some(symbol)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || object_record.flags() != TypeFlags::OBJECT
        || !object_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || object_record.symbol() != Some(symbol)
        || object_record.alias().is_some()
        || declaration_record.kind != SyntaxKind::VariableDeclaration
        || variable.initializer.is_some()
        || bound
            .symbol(declaration)
            .and_then(|declared| store.get_merged_symbol(declared))
            != Some(symbol)
        || annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.parent != Some(declaration.node)
        || reference.type_arguments.is_some()
        || annotation_name_record.kind != SyntaxKind::Identifier
        || annotation_name_record.parent != Some(annotation.node)
        || annotation_identifier.text != constructor_name
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(constructor_name)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_declarations.is_empty()
        || signature_record.flags() != SymbolFlags::SIGNATURE
        || signature_record.check_flags() != CheckFlags::NONE
        || signature_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || signature_declarations.is_empty()
    {
        return Err(reject());
    }

    for signature_declaration in signature_declarations {
        let Some(record) = host.node(*signature_declaration) else {
            continue;
        };
        let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
            continue;
        };
        let [parameter] = signature.parameters.nodes.as_slice() else {
            continue;
        };
        let parameter = NodeRef::new(
            signature_declaration.arena,
            signature_declaration.file,
            *parameter,
        );
        let Some(parameter_record) = host.node(parameter) else {
            continue;
        };
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            continue;
        };
        let Some(question) = parameter_data.question_token else {
            continue;
        };
        let question = NodeRef::new(parameter.arena, parameter.file, question);
        let Some(question_record) = host.node(question) else {
            continue;
        };
        let Some(type_node) = parameter_data.type_ else {
            continue;
        };
        let type_node = NodeRef::new(parameter.arena, parameter.file, type_node);
        let Some(type_record) = host.node(type_node) else {
            continue;
        };
        let Some(return_node) = signature.type_ else {
            continue;
        };
        let return_node = NodeRef::new(
            signature_declaration.arena,
            signature_declaration.file,
            return_node,
        );
        let Some(return_record) = host.node(return_node) else {
            continue;
        };
        let NodeData::TypeReferenceNode(return_reference) = &return_record.data else {
            continue;
        };
        let return_name = NodeRef::new(
            return_node.arena,
            return_node.file,
            return_reference.type_name,
        );
        let Some(return_name_record) = host.node(return_name) else {
            continue;
        };
        let NodeData::Identifier(return_identifier) = &return_name_record.data else {
            continue;
        };
        let Some(parameter_symbol) = host
            .bound_file(parameter)
            .and_then(|bound| bound.symbol(parameter))
            .and_then(|parameter| store.get_merged_symbol(parameter))
        else {
            continue;
        };
        let Some(parameter_symbol_record) = store.symbol(parameter_symbol) else {
            continue;
        };
        if record.kind != SyntaxKind::ConstructSignature
            || !owner_declarations.iter().any(|owner_declaration| {
                record.parent == Some(owner_declaration.node)
                    && signature_declaration.arena == owner_declaration.arena
                    && signature_declaration.file == owner_declaration.file
            })
            || parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(signature_declaration.node)
            || parameter_data.initializer.is_some()
            || parameter_data.dot_dot_dot_token.is_some()
            || question_record.kind != SyntaxKind::QuestionToken
            || question_record.parent != Some(parameter.node)
            || type_record.kind != SyntaxKind::AnyKeyword
            || type_record.parent != Some(parameter.node)
            || !matches!(type_record.data, NodeData::KeywordTypeNode(_))
            || return_record.kind != SyntaxKind::TypeReference
            || return_record.parent != Some(signature_declaration.node)
            || return_reference.type_arguments.is_some()
            || return_name_record.kind != SyntaxKind::Identifier
            || return_name_record.parent != Some(return_node.node)
            || return_identifier.text != instance_name
            || parameter_symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || parameter_symbol_record.check_flags() != CheckFlags::NONE
            || parameter_symbol_record.declarations() != Some(&[parameter])
            || parameter_symbol_record.value_declaration() != Some(parameter)
            || parameter_symbol_record.parent().is_some()
            || parameter_symbol_record.exports().is_some()
            || parameter_symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(parameter_symbol) != Some(parameter_symbol)
        {
            continue;
        }
        return Ok(SourceGlobalObjectConstructorPlan {
            annotation,
            owner,
            declaration: *signature_declaration,
            return_annotation: return_node,
            parameter: SourceNewParameter {
                symbol: parameter_symbol,
                type_: bootstrap.any_type,
            },
            object_type,
        });
    }

    Err(reject())
}

fn plan_global_date_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<SourceGlobalDateConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(reject)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(reject)?;
    let date = store.symbol(symbol).ok_or_else(reject)?;
    let allowed_date_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let declaration = date.value_declaration().ok_or_else(reject)?;
    let (arena, bound) = host.source(declaration).ok_or_else(reject)?;
    let declaration_record = arena.get(declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(reject)?;
    let annotation_record = arena.get(annotation.node).ok_or_else(reject)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(reject());
    };
    let annotation_name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let annotation_name_record = arena.get(annotation_name.node).ok_or_else(reject)?;
    let NodeData::Identifier(annotation_identifier) = &annotation_name_record.data else {
        return Err(reject());
    };
    let owner = globals
        .get_source("DateConstructor")
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or_else(reject)?;
    let owner_record = store.symbol(owner).ok_or_else(reject)?;
    let owner_declarations = owner_record.declarations().ok_or_else(reject)?;
    let signature_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|signature| store.get_merged_symbol(signature))
        .ok_or_else(reject)?;
    let signature_record = store.symbol(signature_symbol).ok_or_else(reject)?;
    let signature_declarations = signature_record.declarations().ok_or_else(reject)?;
    if date.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || !date.flags().contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || date.flags().without(allowed_date_flags) != SymbolFlags::NONE
        || date.check_flags() != CheckFlags::NONE
        || date.name().as_utf8() != Some("Date")
        || date.parent().is_some()
        || date.exports().is_some()
        || date.export_symbol().is_some()
        || globals
            .get_source("Date")
            .and_then(|global| store.get_merged_symbol(global))
            != Some(symbol)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || declaration_record.kind != SyntaxKind::VariableDeclaration
        || variable.initializer.is_some()
        || bound
            .symbol(declaration)
            .and_then(|declared| store.get_merged_symbol(declared))
            != Some(symbol)
        || annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.parent != Some(declaration.node)
        || reference.type_arguments.is_some()
        || annotation_name_record.kind != SyntaxKind::Identifier
        || annotation_name_record.parent != Some(annotation.node)
        || annotation_identifier.text != "DateConstructor"
        || owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("DateConstructor")
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_declarations.is_empty()
        || signature_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::SIGNATURE
        || signature_record.check_flags() != CheckFlags::NONE
        || signature_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || signature_declarations.is_empty()
    {
        return Err(reject());
    }

    for provider in [symbol, owner] {
        if store
            .declared_type_links(provider)
            .and_then(|links| links.declared_type)
            .is_some()
            && (store.declared_type_initialization_in_progress(provider)
                || preflight_class_or_interface_reference(
                    store,
                    host,
                    provider,
                    store.symbol(provider).ok_or_else(reject)?.flags(),
                )? != 0)
        {
            return Err(reject());
        }
    }

    let mut groups: Vec<(NodeRef, Vec<NodeRef>)> = Vec::new();
    for &signature_declaration in signature_declarations {
        let record = host.node(signature_declaration).ok_or_else(reject)?;
        let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
            return Err(reject());
        };
        let parent = NodeRef::new(
            signature_declaration.arena,
            signature_declaration.file,
            record.parent.ok_or_else(reject)?,
        );
        if record.kind != SyntaxKind::ConstructSignature || !owner_declarations.contains(&parent) {
            return Err(reject());
        }
        if !signature.parameters.nodes.is_empty()
            && !date_constructor_has_required_argument(
                store,
                host,
                signature_declaration,
                &signature.parameters.nodes,
            )?
        {
            // Optional, rest, and unresolved parameter types can accept zero
            // arguments or reorder as literal overloads. Do not skip them.
            return Err(reject());
        }
        if let Some((last_parent, declarations)) = groups.last_mut()
            && *last_parent == parent
        {
            declarations.push(signature_declaration);
        } else {
            groups.push((parent, vec![signature_declaration]));
        }
    }

    // reorderCandidates puts later declaration groups first and keeps the
    // signature order inside each group. Required parameters cannot match new().
    for signature_declaration in groups
        .into_iter()
        .rev()
        .flat_map(|(_, declarations)| declarations)
    {
        let record = host.node(signature_declaration).ok_or_else(reject)?;
        let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
            return Err(reject());
        };
        if !signature.parameters.nodes.is_empty() {
            continue;
        }
        let return_annotation = signature.type_.ok_or_else(reject)?;
        let return_annotation = NodeRef::new(
            signature_declaration.arena,
            signature_declaration.file,
            return_annotation,
        );
        let return_record = host.node(return_annotation).ok_or_else(reject)?;
        let NodeData::TypeReferenceNode(return_reference) = &return_record.data else {
            return Err(reject());
        };
        let return_name = NodeRef::new(
            return_annotation.arena,
            return_annotation.file,
            return_reference.type_name,
        );
        let return_name_record = host.node(return_name).ok_or_else(reject)?;
        let NodeData::Identifier(return_identifier) = &return_name_record.data else {
            return Err(reject());
        };
        if record.kind != SyntaxKind::ConstructSignature
            || !owner_declarations.iter().any(|owner_declaration| {
                record.parent == Some(owner_declaration.node)
                    && signature_declaration.arena == owner_declaration.arena
                    && signature_declaration.file == owner_declaration.file
            })
            || !signature.parameters.nodes.is_empty()
            || signature.type_parameters.is_some()
            || return_record.kind != SyntaxKind::TypeReference
            || return_record.parent != Some(signature_declaration.node)
            || return_reference.type_arguments.is_some()
            || return_name_record.kind != SyntaxKind::Identifier
            || return_name_record.parent != Some(return_annotation.node)
            || return_identifier.text != "Date"
        {
            return Err(reject());
        }
        return Ok(SourceGlobalDateConstructorPlan {
            annotation,
            owner,
            declaration: signature_declaration,
            return_annotation,
        });
    }

    Err(reject())
}

fn date_constructor_has_required_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameters: &[ts_ast::NodeId],
) -> Result<bool, SourceNewError> {
    for &parameter in parameters {
        let parameter = NodeRef::new(declaration.arena, declaration.file, parameter);
        let record = host
            .node(parameter)
            .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(parameter)))?;
        let NodeData::ParameterDeclaration(data) = &record.data else {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                parameter,
            )));
        };
        if record.parent != Some(declaration.node) || record.kind != SyntaxKind::Parameter {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                parameter,
            )));
        }
        if data.question_token.is_some()
            || data.dot_dot_dot_token.is_some()
            || data.initializer.is_some()
        {
            continue;
        }
        let Some(annotation) = data.type_ else {
            continue;
        };
        let annotation = NodeRef::new(parameter.arena, parameter.file, annotation);
        if date_constructor_parameter_type_has_no_void(store, host, annotation)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn date_constructor_parameter_type_has_no_void(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, SourceNewError> {
    let record = host
        .node(node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    match &record.data {
        NodeData::KeywordTypeNode(_) => Ok(record.kind != SyntaxKind::VoidKeyword),
        NodeData::LiteralTypeNode(_)
        | NodeData::ArrayTypeNode(_)
        | NodeData::TupleTypeNode(_)
        | NodeData::TypeLiteralNode(_)
        | NodeData::FunctionTypeNode(_)
        | NodeData::ConstructorTypeNode(_) => Ok(true),
        NodeData::ParenthesizedTypeNode(parenthesized) => {
            date_constructor_parameter_type_has_no_void(
                store,
                host,
                NodeRef::new(node.arena, node.file, parenthesized.type_),
            )
        }
        NodeData::UnionTypeNode(union) => {
            for &type_ in &union.types.nodes {
                if !date_constructor_parameter_type_has_no_void(
                    store,
                    host,
                    NodeRef::new(node.arena, node.file, type_),
                )? {
                    return Ok(false);
                }
            }
            Ok(!union.types.nodes.is_empty())
        }
        NodeData::TypeReferenceNode(reference) => {
            let name = NodeRef::new(node.arena, node.file, reference.type_name);
            let Some(NodeData::Identifier(identifier)) = host.node(name).map(|node| &node.data)
            else {
                return Ok(false);
            };
            let (arena, bound) = host
                .source(name)
                .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(name)))?;
            let mut callback_host = host.name_resolver_host(store)?;
            let symbol =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .resolve(
                        Some(CanonicalResolutionLocation::Bound(name)),
                        &identifier.text,
                        SymbolFlags::TYPE,
                        None,
                        false,
                        false,
                    )
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .and_then(|symbol| store.get_merged_symbol(symbol));
            Ok(symbol
                .and_then(|symbol| store.symbol(symbol))
                .is_some_and(|symbol| {
                    symbol
                        .flags()
                        .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
                }))
        }
        _ => Ok(false),
    }
}

#[allow(clippy::too_many_lines)] // Preserve the global, generic signature, and executor proof.
fn plan_global_promise_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    executor: NodeRef,
) -> Result<SourceGlobalPromiseConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(reject)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(reject)?;
    let promise = store.symbol(symbol).ok_or_else(reject)?;
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let variable_declaration = promise.value_declaration().ok_or_else(reject)?;
    let (arena, bound) = host.source(variable_declaration).ok_or_else(reject)?;
    let variable_record = arena.get(variable_declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &variable_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(variable_declaration.arena, variable_declaration.file, node))
        .ok_or_else(reject)?;
    let annotation_record = host.node(annotation).ok_or_else(reject)?;
    let NodeData::TypeReferenceNode(annotation_reference) = &annotation_record.data else {
        return Err(reject());
    };
    let annotation_name = NodeRef::new(
        annotation.arena,
        annotation.file,
        annotation_reference.type_name,
    );
    let annotation_name_record = host.node(annotation_name).ok_or_else(reject)?;
    let NodeData::Identifier(annotation_identifier) = &annotation_name_record.data else {
        return Err(reject());
    };
    let owner = globals
        .get_source("PromiseConstructor")
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or_else(reject)?;
    let owner_record = store.symbol(owner).ok_or_else(reject)?;
    let owner_declarations = owner_record.declarations().ok_or_else(reject)?;
    let constructor_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|signature| store.get_merged_symbol(signature))
        .ok_or_else(reject)?;
    let constructor_record = store.symbol(constructor_symbol).ok_or_else(reject)?;
    let declarations = constructor_record.declarations().ok_or_else(reject)?;
    if promise.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || !promise
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || promise.flags().without(allowed_flags) != SymbolFlags::NONE
        || promise.check_flags() != CheckFlags::NONE
        || promise.name().as_utf8() != Some("Promise")
        || promise.parent().is_some()
        || promise.exports().is_some()
        || promise.export_symbol().is_some()
        || globals
            .get_source("Promise")
            .and_then(|global| store.get_merged_symbol(global))
            != Some(symbol)
        || variable_record.kind != SyntaxKind::VariableDeclaration
        || variable.initializer.is_some()
        || bound
            .symbol(variable_declaration)
            .and_then(|declared| store.get_merged_symbol(declared))
            != Some(symbol)
        || annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.parent != Some(variable_declaration.node)
        || annotation_reference.type_arguments.is_some()
        || annotation_name_record.kind != SyntaxKind::Identifier
        || annotation_name_record.parent != Some(annotation.node)
        || annotation_identifier.text != "PromiseConstructor"
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("PromiseConstructor")
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_declarations.is_empty()
        || constructor_record.flags() != SymbolFlags::SIGNATURE
        || constructor_record.check_flags() != CheckFlags::NONE
        || constructor_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || declarations.is_empty()
    {
        return Err(reject());
    }

    for &declaration in declarations {
        let Some(record) = host.node(declaration) else {
            continue;
        };
        let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
            continue;
        };
        let Some(type_parameters) = signature.type_parameters.as_ref() else {
            continue;
        };
        let [type_parameter] = type_parameters.nodes.as_slice() else {
            continue;
        };
        let [parameter] = signature.parameters.nodes.as_slice() else {
            continue;
        };
        let type_parameter = NodeRef::new(declaration.arena, declaration.file, *type_parameter);
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let Some(type_parameter_record) = host.node(type_parameter) else {
            continue;
        };
        let NodeData::TypeParameterDeclaration(type_parameter_data) = &type_parameter_record.data
        else {
            continue;
        };
        let Some(parameter_record) = host.node(parameter) else {
            continue;
        };
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            continue;
        };
        let Some(parameter_annotation) = parameter_data.type_ else {
            continue;
        };
        let parameter_annotation =
            NodeRef::new(declaration.arena, declaration.file, parameter_annotation);
        let Some(parameter_annotation_record) = host.node(parameter_annotation) else {
            continue;
        };
        let Some(return_annotation) = signature.type_ else {
            continue;
        };
        let return_annotation =
            NodeRef::new(declaration.arena, declaration.file, return_annotation);
        let Some(return_record) = host.node(return_annotation) else {
            continue;
        };
        let NodeData::TypeReferenceNode(return_reference) = &return_record.data else {
            continue;
        };
        let return_name = NodeRef::new(
            declaration.arena,
            declaration.file,
            return_reference.type_name,
        );
        let Some(return_name_record) = host.node(return_name) else {
            continue;
        };
        let NodeData::Identifier(return_identifier) = &return_name_record.data else {
            continue;
        };
        let Some(return_arguments) = return_reference.type_arguments.as_ref() else {
            continue;
        };
        let [return_argument] = return_arguments.nodes.as_slice() else {
            continue;
        };
        let return_argument = NodeRef::new(declaration.arena, declaration.file, *return_argument);
        let Some(return_argument_record) = host.node(return_argument) else {
            continue;
        };
        let NodeData::TypeReferenceNode(return_parameter) = &return_argument_record.data else {
            continue;
        };
        let return_parameter_name = NodeRef::new(
            declaration.arena,
            declaration.file,
            return_parameter.type_name,
        );
        let Some(return_parameter_record) = host.node(return_parameter_name) else {
            continue;
        };
        let NodeData::Identifier(return_parameter_identifier) = &return_parameter_record.data
        else {
            continue;
        };
        let type_parameter_name = NodeRef::new(
            declaration.arena,
            declaration.file,
            type_parameter_data.name,
        );
        let Some(type_parameter_name_record) = host.node(type_parameter_name) else {
            continue;
        };
        let NodeData::Identifier(type_parameter_identifier) = &type_parameter_name_record.data
        else {
            continue;
        };
        let Some(type_parameter_symbol) = host
            .bound_file(type_parameter)
            .and_then(|bound| bound.symbol(type_parameter))
            .and_then(|symbol| store.get_merged_symbol(symbol))
        else {
            continue;
        };
        let Some(parameter_symbol) = host
            .bound_file(parameter)
            .and_then(|bound| bound.symbol(parameter))
            .and_then(|symbol| store.get_merged_symbol(symbol))
        else {
            continue;
        };
        let Ok(executor_plan) =
            plan_function_type(store, host, parameter_annotation, None, false, None)
        else {
            continue;
        };
        let [resolve, reject_parameter] = executor_plan.parameters.as_slice() else {
            continue;
        };
        let Ok(resolve_plan) =
            plan_function_type(store, host, resolve.type_node, None, false, None)
        else {
            continue;
        };
        let Ok(reject_plan) =
            plan_function_type(store, host, reject_parameter.type_node, None, false, None)
        else {
            continue;
        };
        if record.kind != SyntaxKind::ConstructSignature
            || !owner_declarations.iter().any(|owner_declaration| {
                record.parent == Some(owner_declaration.node)
                    && declaration.arena == owner_declaration.arena
                    && declaration.file == owner_declaration.file
            })
            || type_parameters.has_trailing_comma
            || type_parameter_record.kind != SyntaxKind::TypeParameter
            || type_parameter_record.parent != Some(declaration.node)
            || type_parameter_data.constraint.is_some()
            || type_parameter_data.default_type.is_some()
            || type_parameter_name_record.parent != Some(type_parameter.node)
            || type_parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_data.initializer.is_some()
            || parameter_data.question_token.is_some()
            || parameter_data.dot_dot_dot_token.is_some()
            || parameter_annotation_record.kind != SyntaxKind::FunctionType
            || parameter_annotation_record.parent != Some(parameter.node)
            || executor_plan.min_argument_count != 2
            || executor_plan.flags != SignatureFlags::NONE
            || host.node(executor_plan.return_type).map(|node| node.kind)
                != Some(SyntaxKind::VoidKeyword)
            || resolve_plan.parameters.len() != 1
            || resolve_plan.min_argument_count != 1
            || host.node(resolve_plan.return_type).map(|node| node.kind)
                != Some(SyntaxKind::VoidKeyword)
            || reject_plan.parameters.len() != 1
            || reject_plan.min_argument_count != 0
            || host.node(reject_plan.return_type).map(|node| node.kind)
                != Some(SyntaxKind::VoidKeyword)
            || return_record.kind != SyntaxKind::TypeReference
            || return_record.parent != Some(declaration.node)
            || return_name_record.kind != SyntaxKind::Identifier
            || return_name_record.parent != Some(return_annotation.node)
            || return_identifier.text != "Promise"
            || return_arguments.has_trailing_comma
            || return_argument_record.kind != SyntaxKind::TypeReference
            || return_argument_record.parent != Some(return_annotation.node)
            || return_parameter.type_arguments.is_some()
            || return_parameter_record.kind != SyntaxKind::Identifier
            || return_parameter_record.parent != Some(return_argument.node)
            || return_parameter_identifier.text != type_parameter_identifier.text
            || store.symbol(type_parameter_symbol).is_none_or(|symbol| {
                symbol.flags() != SymbolFlags::TYPE_PARAMETER
                    || symbol.check_flags() != CheckFlags::NONE
                    || symbol.declarations() != Some(&[type_parameter])
            })
            || store.symbol(parameter_symbol).is_none_or(|symbol| {
                symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    || symbol.check_flags() != CheckFlags::NONE
                    || symbol.declarations() != Some(&[parameter])
                    || symbol.value_declaration() != Some(parameter)
            })
        {
            continue;
        }
        return Ok(SourceGlobalPromiseConstructorPlan {
            annotation,
            owner,
            declaration,
            type_parameter: type_parameter_symbol,
            parameter: parameter_symbol,
            parameter_annotation,
            return_annotation,
            executor,
        });
    }

    Err(reject())
}

#[allow(clippy::too_many_arguments)] // Keeps constructor syntax and binder ownership explicit.
fn plan_global_array_constructor(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    first_argument: Option<&SourceNewArgument>,
    additional_arguments: &[SourceNewArgument],
) -> Result<SourceGlobalArrayConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(reject)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(reject)?;
    let array = store.symbol(symbol).ok_or_else(reject)?;
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let array_target = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .ok_or_else(reject)?;
    let array_record = store.type_payload(array_target).ok_or_else(reject)?;
    let TypeData::Interface(array_interface) = array_record.data() else {
        return Err(reject());
    };
    let declaration = array.value_declaration().ok_or_else(reject)?;
    let (library_arena, bound) = host.source(declaration).ok_or_else(reject)?;
    let declaration_record = library_arena.get(declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        .ok_or_else(reject)?;
    let annotation_record = host.node(annotation).ok_or_else(reject)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(reject());
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = host.node(name).ok_or_else(reject)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(reject());
    };
    let owner = globals
        .get_source("ArrayConstructor")
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or_else(reject)?;
    let owner_record = store.symbol(owner).ok_or_else(reject)?;
    let owner_declarations = owner_record.declarations().ok_or_else(reject)?;
    let constructor_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(reject)?;
    let signatures = store.symbol(constructor_symbol).ok_or_else(reject)?;
    let declarations = signatures.declarations().ok_or_else(reject)?;
    if array.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || !array
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || array.flags().without(allowed_flags) != SymbolFlags::NONE
        || array.check_flags() != CheckFlags::NONE
        || array.name().as_utf8() != Some("Array")
        || array.parent().is_some()
        || array.exports().is_some()
        || array.export_symbol().is_some()
        || array_record.flags() != TypeFlags::OBJECT
        || !array_record.object_flags().contains(ObjectFlags::INTERFACE)
        || array_record.symbol() != Some(symbol)
        || array_record.alias().is_some()
        || array_interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_none_or(|arguments| arguments.len() != 1)
        || declaration_record.kind != SyntaxKind::VariableDeclaration
        || variable.initializer.is_some()
        || bound
            .symbol(declaration)
            .and_then(|declared| store.get_merged_symbol(declared))
            != Some(symbol)
        || annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.parent != Some(declaration.node)
        || reference.type_arguments.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(annotation.node)
        || identifier.text != "ArrayConstructor"
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("ArrayConstructor")
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_declarations.is_empty()
        || signatures.flags() != SymbolFlags::SIGNATURE
        || signatures.check_flags() != CheckFlags::NONE
        || signatures
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || declarations.len() < 3
    {
        return Err(reject());
    }

    let mut length = None;
    let mut generic_length = None;
    let mut items = None;
    for &declaration in declarations {
        let Some(signature_record) = host.node(declaration) else {
            continue;
        };
        let NodeData::ConstructSignatureDeclaration(signature) = &signature_record.data else {
            continue;
        };
        let [parameter_node] = signature.parameters.nodes.as_slice() else {
            continue;
        };
        let parameter_node = NodeRef::new(declaration.arena, declaration.file, *parameter_node);
        let Some(parameter_record) = host.node(parameter_node) else {
            continue;
        };
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            continue;
        };
        let Some(parameter_annotation) = parameter_data.type_ else {
            continue;
        };
        let parameter_annotation = NodeRef::new(
            parameter_node.arena,
            parameter_node.file,
            parameter_annotation,
        );
        let Some(parameter_annotation_record) = host.node(parameter_annotation) else {
            continue;
        };
        let Some(return_annotation) = signature.type_ else {
            continue;
        };
        let return_annotation =
            NodeRef::new(declaration.arena, declaration.file, return_annotation);
        let Some(return_record) = host.node(return_annotation) else {
            continue;
        };
        let NodeData::ArrayTypeNode(return_array) = &return_record.data else {
            continue;
        };
        let return_element = NodeRef::new(
            return_annotation.arena,
            return_annotation.file,
            return_array.element_type,
        );
        let Some(return_element_record) = host.node(return_element) else {
            continue;
        };
        let Some(parameter) = host
            .bound_file(parameter_node)
            .and_then(|bound| bound.symbol(parameter_node))
            .and_then(|parameter| store.get_merged_symbol(parameter))
        else {
            continue;
        };
        let Some(parameter_symbol) = store.symbol(parameter) else {
            continue;
        };
        let type_parameter = match signature.type_parameters.as_ref() {
            None => None,
            Some(parameters) if parameters.nodes.len() == 1 => {
                let declaration =
                    NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
                let Some(symbol) = host
                    .bound_file(declaration)
                    .and_then(|bound| bound.symbol(declaration))
                    .and_then(|parameter| store.get_merged_symbol(parameter))
                else {
                    continue;
                };
                let Some(record) = store.symbol(symbol) else {
                    continue;
                };
                if record.flags() != SymbolFlags::TYPE_PARAMETER
                    || record.check_flags() != CheckFlags::NONE
                    || record.declarations() != Some(&[declaration])
                {
                    continue;
                }
                Some(symbol)
            }
            Some(_) => continue,
        };
        if signature_record.kind != SyntaxKind::ConstructSignature
            || !owner_declarations.iter().any(|owner_declaration| {
                signature_record.parent == Some(owner_declaration.node)
                    && declaration.arena == owner_declaration.arena
                    && declaration.file == owner_declaration.file
            })
            || parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_data.initializer.is_some()
            || parameter_annotation_record.parent != Some(parameter_node.node)
            || return_record.kind != SyntaxKind::ArrayType
            || return_record.parent != Some(declaration.node)
            || return_element_record.parent != Some(return_annotation.node)
            || parameter_symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || parameter_symbol.check_flags() != CheckFlags::NONE
            || parameter_symbol.declarations() != Some(&[parameter_node])
            || parameter_symbol.value_declaration() != Some(parameter_node)
            || parameter_symbol.parent().is_some()
            || parameter_symbol.exports().is_some()
            || parameter_symbol.export_symbol().is_some()
        {
            continue;
        }

        let planned = SourceGlobalArraySignaturePlan {
            declaration,
            parameter,
            parameter_annotation,
            return_annotation,
            type_parameter,
        };
        match (
            type_parameter,
            parameter_data.question_token.is_some(),
            parameter_data.dot_dot_dot_token.is_some(),
            parameter_annotation_record.kind,
            return_element_record.kind,
        ) {
            (None, true, false, SyntaxKind::NumberKeyword, SyntaxKind::AnyKeyword)
                if length.is_none() =>
            {
                length = Some(planned);
            }
            (Some(_), false, false, SyntaxKind::NumberKeyword, SyntaxKind::TypeReference)
                if generic_length.is_none() =>
            {
                generic_length = Some(planned);
            }
            (Some(_), false, true, SyntaxKind::ArrayType, SyntaxKind::TypeReference)
                if items.is_none() =>
            {
                items = Some(planned);
            }
            _ => {}
        }
    }
    let (Some(length), Some(generic_length), Some(items)) = (length, generic_length, items) else {
        return Err(reject());
    };

    let record = arena.get(node.node).ok_or_else(reject)?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Err(reject());
    };
    let explicit_element = if let Some(arguments) = expression.type_arguments.as_ref() {
        let [argument] = arguments.nodes.as_slice() else {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
        };
        if arguments.has_trailing_comma {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
        }
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = arena.get(argument.node).ok_or_else(reject)?;
        if argument_record.parent != Some(node.node) {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
        }
        match argument_record.kind {
            SyntaxKind::StringKeyword => Some(bootstrap.string_type),
            SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
            SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
            SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
            _ => return Err(unsupported(SourceNewUnsupported::TypeArguments(argument))),
        }
    } else {
        None
    };
    let argument_count = usize::from(first_argument.is_some()) + additional_arguments.len();
    let selection = match (argument_count, first_argument, explicit_element) {
        (0, _, None) => SourceGlobalArraySelection::Length,
        (0, _, Some(element)) => SourceGlobalArraySelection::Items(element),
        (1, Some(argument), None)
            if matches!(&argument.value, SourceNewArgumentValue::Number(_)) =>
        {
            SourceGlobalArraySelection::Length
        }
        (1, Some(argument), Some(element))
            if matches!(&argument.value, SourceNewArgumentValue::Number(_)) =>
        {
            SourceGlobalArraySelection::GenericLength(element)
        }
        (_, Some(argument), explicit) => {
            let inferred = match &argument.value {
                SourceNewArgumentValue::String(_) => bootstrap.string_type,
                SourceNewArgumentValue::Number(_) => bootstrap.number_type,
                SourceNewArgumentValue::Boolean(_) => bootstrap.boolean_type,
                SourceNewArgumentValue::EmptyObject(_) => bootstrap.empty_type_literal_type,
            };
            let element = explicit.unwrap_or(inferred);
            if std::iter::once(argument)
                .chain(additional_arguments)
                .any(|argument| {
                    let actual = match &argument.value {
                        SourceNewArgumentValue::String(_) => bootstrap.string_type,
                        SourceNewArgumentValue::Number(_) => bootstrap.number_type,
                        SourceNewArgumentValue::Boolean(_) => bootstrap.boolean_type,
                        SourceNewArgumentValue::EmptyObject(_) => bootstrap.empty_type_literal_type,
                    };
                    element != bootstrap.any_type && element != actual
                })
            {
                return Err(unsupported(SourceNewUnsupported::Arguments(node)));
            }
            SourceGlobalArraySelection::Items(element)
        }
        _ => return Err(unsupported(SourceNewUnsupported::Arguments(node))),
    };

    Ok(SourceGlobalArrayConstructorPlan {
        annotation,
        owner,
        array_target,
        length,
        generic_length,
        items,
        selection,
    })
}

#[allow(clippy::too_many_arguments)]
fn plan_declared_constructor(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    argument: Option<&SourceNewArgument>,
) -> Result<SourceDeclaredConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let owner = store.symbol(symbol).ok_or_else(reject)?;
    let Some([declaration]) = owner.declarations() else {
        return Err(reject());
    };
    let declaration = *declaration;
    let declaration_record = arena.get(declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(reject());
    };
    let list = declaration_record
        .parent
        .map(|list| NodeRef::new(declaration.arena, declaration.file, list))
        .ok_or_else(reject)?;
    let list_record = arena.get(list.node).ok_or_else(reject)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(reject());
    };
    let statement = list_record
        .parent
        .map(|statement| NodeRef::new(declaration.arena, declaration.file, statement))
        .ok_or_else(reject)?;
    let statement_record = arena.get(statement.node).ok_or_else(reject)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(reject());
    };
    let Some(modifiers) = statement_data.modifiers.as_ref() else {
        return Err(reject());
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Err(reject());
    };
    let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier);
    let modifier_record = arena.get(modifier.node).ok_or_else(reject)?;
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = arena.get(name.node).ok_or_else(reject)?;
    let NodeData::Identifier(name_data) = &name_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        .ok_or_else(reject)?;
    let annotation_record = arena.get(annotation.node).ok_or_else(reject)?;
    let construction = arena.get(node.node).ok_or_else(reject)?;

    if !declaration.is_for(node.arena, node.file)
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(declaration)
        || owner.name().as_utf8() != Some(name_data.text.as_str())
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || bound.symbol(declaration) != Some(symbol)
        || declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(list.node)
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || !matches!(list_record.flags.0, 0..=2)
        || declarations.declarations.has_trailing_comma
        || !declarations.declarations.nodes.contains(&declaration.node)
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(bound.source_file().node)
        || statement_record.range.end > construction.range.start
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifier_record.kind != SyntaxKind::DeclareKeyword
        || modifier_record.flags.0 != 0
        || modifier_record.parent != Some(statement.node)
        || !matches!(modifier_record.data, NodeData::Token(_))
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || name_data.flow_node.is_some()
        || name_data.text.is_empty()
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
    {
        return Err(reject());
    }

    let object = plan_declared_constructor_object(arena, bound, store, host, annotation)
        .map_err(|_| reject())?;
    let authenticated_prototype = matches!(
        object.properties.as_slice(),
        [prototype]
            if prototype.name.as_utf8() == Some("prototype")
                && prototype.readonly
                && object.call_signatures.iter().any(|signature| {
                    host.node(signature.declaration).is_some_and(|record| {
                        record.kind == SyntaxKind::ConstructSignature
                            && store.source_node_kind(signature.return_type)
                                == store.source_node_kind(prototype.type_node)
                    })
                })
    );
    if object.call_signatures.is_empty()
        || !object.properties.is_empty() && !authenticated_prototype
        || !object.methods.is_empty()
        || !object.spreads.is_empty()
        || !object.indexes.is_empty()
        || object.heritage.is_some()
        || !object.call_signatures.iter().any(|signature| {
            host.node(signature.declaration)
                .is_some_and(|record| record.kind == SyntaxKind::ConstructSignature)
        })
    {
        return Err(reject());
    }

    for signature in object.call_signatures {
        if host
            .node(signature.declaration)
            .is_none_or(|record| record.kind != SyntaxKind::ConstructSignature)
        {
            continue;
        }
        let supplied_arguments = usize::from(argument.is_some());
        if signature.parameters.len() > 1
            || supplied_arguments < signature.min_argument_count()
            || supplied_arguments > signature.parameters.len()
        {
            continue;
        }
        let signature_parameter = signature
            .parameters
            .first()
            .map(|parameter| {
                declared_constructor_parameter_type(store, host, parameter.type_node).map(|type_| {
                    type_.map(|type_| SourceNewParameter {
                        symbol: parameter.symbol,
                        type_,
                    })
                })
            })
            .transpose()?
            .flatten();
        if signature.parameters.len() != usize::from(signature_parameter.is_some()) {
            return Err(reject());
        }
        let parameter = argument.and(signature_parameter);
        if argument
            .zip(parameter)
            .is_some_and(|(argument, parameter)| {
                !argument_matches_parameter(store, argument, parameter)
            })
        {
            continue;
        }
        return Ok(SourceDeclaredConstructorPlan {
            annotation,
            declaration: signature.declaration,
            parameter,
            signature_parameter,
            min_argument_count: signature.min_argument_count(),
        });
    }

    Err(unsupported(SourceNewUnsupported::Arguments(node)))
}

#[allow(clippy::too_many_arguments)] // The ambient declaration and union share one source proof.
fn plan_declared_class_union_constructor(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    node: NodeRef,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<SourceClassUnionConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let owner = store.symbol(symbol).ok_or_else(reject)?;
    let Some([declaration]) = owner.declarations() else {
        return Err(reject());
    };
    let declaration = *declaration;
    let declaration_record = arena.get(declaration.node).ok_or_else(reject)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(reject());
    };
    let list = declaration_record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
        .ok_or_else(reject)?;
    let list_record = arena.get(list.node).ok_or_else(reject)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(reject());
    };
    let statement = list_record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
        .ok_or_else(reject)?;
    let statement_record = arena.get(statement.node).ok_or_else(reject)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(reject());
    };
    let Some(modifiers) = statement_data.modifiers.as_ref() else {
        return Err(reject());
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Err(reject());
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
    let modifier_record = arena.get(modifier.node).ok_or_else(reject)?;
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = arena.get(name.node).ok_or_else(reject)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(reject)?;
    let annotation_record = arena.get(annotation.node).ok_or_else(reject)?;
    let construction = arena.get(node.node).ok_or_else(reject)?;
    if !declaration.is_for(node.arena, node.file)
        || !matches!(
            owner.flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
        )
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some(identifier.text.as_str())
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || bound.symbol(declaration) != Some(symbol)
        || declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || !declarations.declarations.nodes.contains(&declaration.node)
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(bound.source_file().node)
        || statement_record.range.end > construction.range.start
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifier_record.kind != SyntaxKind::DeclareKeyword
        || modifier_record.flags.0 != 0
        || modifier_record.parent != Some(statement.node)
        || !matches!(modifier_record.data, NodeData::Token(_))
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
    {
        return Err(reject());
    }

    let mut classes = Vec::new();
    let mut aliases = HashSet::new();
    collect_class_union_constructors(
        arena,
        bound,
        store,
        host,
        prior_classes,
        annotation,
        &mut aliases,
        &mut classes,
    )
    .map_err(|_| reject())?;
    if classes.len() < 2 {
        return Err(reject());
    }
    Ok(SourceClassUnionConstructorPlan {
        provider: SourceClassUnionConstructorProvider::Ambient(annotation),
        classes,
    })
}

#[allow(clippy::too_many_arguments)] // Callback, parameter, receiver, and class provenance are inseparable.
fn plan_callback_class_union_constructor(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    node: NodeRef,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<Option<SourceClassUnionConstructorPlan>, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let owner = store.symbol(symbol).ok_or_else(reject)?;
    let Some([parameter]) = owner.declarations() else {
        return Ok(None);
    };
    let parameter = *parameter;
    let Some(parameter_record) = arena.get(parameter.node) else {
        return Ok(None);
    };
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(None);
    };
    let arrow = parameter_record
        .parent
        .map(|parent| NodeRef::new(parameter.arena, parameter.file, parent))
        .ok_or_else(reject)?;
    let arrow_record = arena.get(arrow.node).ok_or_else(reject)?;
    let NodeData::ArrowFunction(callback) = &arrow_record.data else {
        return Err(reject());
    };
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = arena.get(name.node).ok_or_else(reject)?;
    let NodeData::Identifier(parameter_name) = &name_record.data else {
        return Err(reject());
    };
    let constructor_record = arena.get(constructor.node).ok_or_else(reject)?;
    let NodeData::Identifier(constructor_name) = &constructor_record.data else {
        return Err(reject());
    };
    let locals = bound
        .locals(arrow)
        .and_then(|locals| store.symbol_table(locals))
        .ok_or_else(reject)?;
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(arrow.node)
        || parameter_data.dot_dot_dot_token.is_some()
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.type_.is_some()
        || parameter_data.facts != 0
        || parameter_data.modifiers.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(parameter.node)
        || parameter_name.flow_node.is_some()
        || parameter_name.text.is_empty()
        || parameter_name.text != constructor_name.text
        || owner.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some(parameter_name.text.as_str())
        || owner.value_declaration() != Some(parameter)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || bound.symbol(parameter) != Some(symbol)
        || locals.len() != 1
        || locals.get_source(&parameter_name.text) != Some(symbol)
        || arrow_record.kind != SyntaxKind::ArrowFunction
        || arrow_record.flags.0 != 0
        || callback.asterisk_token.is_some()
        || callback.body != node.node
        || callback.flow_node.is_some()
        || callback.full_signature.is_some()
        || callback.symbol.is_some()
        || callback.type_.is_some()
        || callback.type_parameters.is_some()
        || callback.facts != 0
        || callback.modifiers.is_some()
        || callback.parameters.has_trailing_comma
        || callback.parameters.nodes.as_slice() != [parameter.node]
        || arena
            .get(node.node)
            .is_none_or(|construction| construction.parent != Some(arrow.node))
        || !source_direct_call_argument_arrow_is_exact(store, host, arrow)
            .map_err(|_| invariant(SourceNewInvariant::InvalidConstructorCache(constructor)))?
    {
        return Err(reject());
    }

    let call = arrow_record
        .parent
        .map(|parent| NodeRef::new(arrow.arena, arrow.file, parent))
        .ok_or_else(reject)?;
    let call_record = arena.get(call.node).ok_or_else(reject)?;
    let NodeData::CallExpression(invocation) = &call_record.data else {
        return Err(reject());
    };
    let property = NodeRef::new(call.arena, call.file, invocation.expression);
    let property_record = arena.get(property.node).ok_or_else(reject)?;
    let NodeData::PropertyAccessExpression(access) = &property_record.data else {
        return Err(reject());
    };
    let method = NodeRef::new(property.arena, property.file, access.name);
    let method_record = arena.get(method.node).ok_or_else(reject)?;
    let NodeData::Identifier(method_name) = &method_record.data else {
        return Err(reject());
    };
    let receiver = NodeRef::new(property.arena, property.file, access.expression);
    let receiver_record = arena.get(receiver.node).ok_or_else(reject)?;
    let NodeData::ArrayLiteralExpression(array) = &receiver_record.data else {
        return Err(reject());
    };
    if call_record.kind != SyntaxKind::CallExpression
        || call_record.flags.0 != 0
        || invocation.question_dot_token.is_some()
        || invocation.symbol.is_some()
        || invocation.type_arguments.is_some()
        || invocation.facts != 0
        || invocation.arguments.has_trailing_comma
        || invocation.arguments.nodes.as_slice() != [arrow.node]
        || property_record.kind != SyntaxKind::PropertyAccessExpression
        || property_record.flags.0 != 0
        || property_record.parent != Some(call.node)
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
        || method_record.kind != SyntaxKind::Identifier
        || method_record.flags.0 != 0
        || method_record.parent != Some(property.node)
        || method_name.flow_node.is_some()
        || method_name.text != "map"
        || receiver_record.kind != SyntaxKind::ArrayLiteralExpression
        || receiver_record.flags.0 != 0
        || receiver_record.parent != Some(property.node)
        || array.facts != 0
        || array.elements.has_trailing_comma
        || array.elements.nodes.len() < 2
    {
        return Err(reject());
    }

    let mut classes = Vec::new();
    classes
        .try_reserve(array.elements.nodes.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(constructor)))?;
    for element in &array.elements.nodes {
        let element = NodeRef::new(receiver.arena, receiver.file, *element);
        let element_record = arena.get(element.node).ok_or_else(reject)?;
        let NodeData::Identifier(identifier) = &element_record.data else {
            return Err(reject());
        };
        if element_record.kind != SyntaxKind::Identifier
            || element_record.flags.0 != 0
            || element_record.parent != Some(receiver.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(reject());
        }
        let mut callback_host = host.name_resolver_host(store)?;
        let class_symbol =
            CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                .map_err(|error| {
                    invariant(SourceNewInvariant::NameResolution {
                        node: element,
                        error,
                    })
                })?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(element)),
                    &identifier.text,
                    SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
                    None,
                    false,
                    false,
                )
                .map_err(|error| {
                    invariant(SourceNewInvariant::NameResolution {
                        node: element,
                        error,
                    })
                })?
                .and_then(|class| store.get_merged_symbol(class))
                .ok_or_else(reject)?;
        let class = prior_classes.get(&class_symbol).ok_or_else(reject)?;
        let class = ClassMemberQueryPlan::Direct(class.clone());
        if class.symbol() != class_symbol
            || class.constructor_visibility() != ClassConstructorVisibility::Public
            || !class.constructor_parameter_symbols().is_empty()
            || class.constructor_minimum_argument_count() != 0
            || classes
                .iter()
                .any(|previous: &ClassMemberQueryPlan| previous.symbol() == class_symbol)
        {
            return Err(reject());
        }
        preflight_nongeneric_class_member_query(store, host, &class)?;
        if exact_symbol_cache(store, element)
            .map_err(|()| invariant(SourceNewInvariant::InvalidConstructorCache(element)))?
            .is_some_and(|cached| cached != class_symbol)
        {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                element,
            )));
        }
        if let Some(cached) = exact_type_cache(store, element)
            .map_err(|()| invariant(SourceNewInvariant::InvalidConstructorCache(element)))?
            && authenticated_class_constructor_value(store, class_symbol)
                .is_none_or(|(value, _)| value != cached)
        {
            return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                element,
            )));
        }
        classes.push(class);
    }

    Ok(Some(SourceClassUnionConstructorPlan {
        provider: SourceClassUnionConstructorProvider::ArrayCallback {
            parameter,
            arrow,
            call,
            receiver,
        },
        classes,
    }))
}

#[allow(clippy::too_many_arguments)] // Every nested alias must preserve the same source ownership.
fn collect_class_union_constructors(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    node: NodeRef,
    aliases: &mut HashSet<SemanticSymbolId>,
    classes: &mut Vec<ClassMemberQueryPlan>,
) -> Result<(), SourceNewError> {
    let reject = || unsupported(SourceNewUnsupported::Constructor(node));
    let record = arena.get(node.node).ok_or_else(reject)?;
    if record.flags.0 != 0 || !bound.contains(node) {
        return Err(reject());
    }
    match &record.data {
        NodeData::UnionTypeNode(union) if record.kind == SyntaxKind::UnionType => {
            if union.types.nodes.len() < 2
                || union.types.has_trailing_comma
                || union.types.range != record.range
            {
                return Err(reject());
            }
            for child in &union.types.nodes {
                let child = NodeRef::new(node.arena, node.file, *child);
                if arena
                    .get(child.node)
                    .is_none_or(|child| child.parent != Some(node.node))
                {
                    return Err(reject());
                }
                collect_class_union_constructors(
                    arena,
                    bound,
                    store,
                    host,
                    prior_classes,
                    child,
                    aliases,
                    classes,
                )?;
            }
        }
        NodeData::TypeReferenceNode(reference)
            if record.kind == SyntaxKind::TypeReference && reference.type_arguments.is_none() =>
        {
            let name = NodeRef::new(node.arena, node.file, reference.type_name);
            let name_record = arena.get(name.node).ok_or_else(reject)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(reject());
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(node.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
            {
                return Err(reject());
            }
            let mut callback_host = host.name_resolver_host(store)?;
            let symbol =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .resolve(
                        Some(CanonicalResolutionLocation::Bound(name)),
                        &identifier.text,
                        SymbolFlags::TYPE,
                        None,
                        false,
                        false,
                    )
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .ok_or_else(reject)?;
            let owner = store.symbol(symbol).ok_or_else(reject)?;
            let Some([declaration]) = owner.declarations() else {
                return Err(reject());
            };
            let declaration = *declaration;
            let declaration_record = arena.get(declaration.node).ok_or_else(reject)?;
            let NodeData::TypeAliasDeclaration(alias) = &declaration_record.data else {
                return Err(reject());
            };
            if owner.flags() != SymbolFlags::TYPE_ALIAS
                || owner.check_flags() != CheckFlags::NONE
                || owner.name().as_utf8() != Some(identifier.text.as_str())
                || owner.value_declaration().is_some()
                || owner.members().is_some()
                || owner.exports().is_some()
                || owner.parent().is_some()
                || owner.export_symbol().is_some()
                || !declaration.is_for(node.arena, node.file)
                || declaration_record.kind != SyntaxKind::TypeAliasDeclaration
                || declaration_record.flags.0 != 0
                || declaration_record.parent != Some(bound.source_file().node)
                || declaration_record.range.end > record.range.start
                || alias.type_parameters.is_some()
                || !host.symbol_matches(store, declaration, symbol)
                || !aliases.insert(symbol)
            {
                return Err(reject());
            }
            let value = NodeRef::new(declaration.arena, declaration.file, alias.type_);
            if arena
                .get(value.node)
                .is_none_or(|value| value.parent != Some(declaration.node))
            {
                return Err(reject());
            }
            collect_class_union_constructors(
                arena,
                bound,
                store,
                host,
                prior_classes,
                value,
                aliases,
                classes,
            )?;
        }
        NodeData::TypeQueryNode(query)
            if record.kind == SyntaxKind::TypeQuery && query.type_arguments.is_none() =>
        {
            let name = NodeRef::new(node.arena, node.file, query.expr_name);
            let name_record = arena.get(name.node).ok_or_else(reject)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(reject());
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(node.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
            {
                return Err(reject());
            }
            let mut callback_host = host.name_resolver_host(store)?;
            let symbol =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .resolve(
                        Some(CanonicalResolutionLocation::Bound(name)),
                        &identifier.text,
                        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
                        None,
                        false,
                        false,
                    )
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .ok_or_else(reject)?;
            let class = prior_classes.get(&symbol).ok_or_else(reject)?;
            let class = ClassMemberQueryPlan::Direct(class.clone());
            if class.symbol() != symbol
                || class.constructor_visibility() != ClassConstructorVisibility::Public
                || !class.constructor_parameter_symbols().is_empty()
                || class.constructor_minimum_argument_count() != 0
                || classes.iter().any(|previous| previous.symbol() == symbol)
            {
                return Err(reject());
            }
            preflight_nongeneric_class_member_query(store, host, &class)?;
            if exact_symbol_cache(store, name)
                .map_err(|()| invariant(SourceNewInvariant::InvalidConstructorCache(name)))?
                .is_some_and(|cached| cached != symbol)
            {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(name)));
            }
            if let Some(cached) = exact_type_cache(store, node)
                .map_err(|()| invariant(SourceNewInvariant::InvalidConstructorCache(node)))?
                && authenticated_class_constructor_value(store, symbol)
                    .is_none_or(|(value, _)| value != cached)
            {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(node)));
            }
            classes.push(class);
        }
        _ => return Err(reject()),
    }
    Ok(())
}

fn plan_declared_constructor_object(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
) -> Result<PropertyObjectPlan, SourceNewError> {
    let reject = || unsupported(SourceNewUnsupported::Constructor(annotation));
    let record = arena.get(annotation.node).ok_or_else(reject)?;
    match &record.data {
        NodeData::TypeLiteralNode(_) if record.kind == SyntaxKind::TypeLiteral => {
            plan_type_literal(store, host, annotation, None).map_err(|_| reject())
        }
        NodeData::TypeReferenceNode(reference)
            if record.kind == SyntaxKind::TypeReference && reference.type_arguments.is_none() =>
        {
            let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
            let name_record = arena.get(name.node).ok_or_else(reject)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(reject());
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(annotation.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
            {
                return Err(reject());
            }

            let mut callback_host = host.name_resolver_host(store)?;
            let mut resolver =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(|error| {
                        invariant(SourceNewInvariant::NameResolution { node: name, error })
                    })?;
            let raw_type_symbol = resolver
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(name)),
                    &identifier.text,
                    SymbolFlags::TYPE,
                    None,
                    false,
                    false,
                )
                .map_err(|error| {
                    invariant(SourceNewInvariant::NameResolution { node: name, error })
                })?
                .ok_or_else(reject)?;
            let symbol = store
                .get_merged_symbol(raw_type_symbol)
                .ok_or_else(reject)?;
            let owner = store.symbol(symbol).ok_or_else(reject)?;
            if symbol != raw_type_symbol || owner.check_flags() != CheckFlags::NONE {
                return Err(reject());
            }
            if owner.flags() == SymbolFlags::INTERFACE {
                return plan_interface(store, host, symbol).map_err(|_| reject());
            }
            if owner.flags() != SymbolFlags::TYPE_ALIAS {
                return Err(reject());
            }
            let Some([declaration]) = owner.declarations() else {
                return Err(reject());
            };
            let declaration = *declaration;
            let declaration_record = host.node(declaration).ok_or_else(reject)?;
            let NodeData::TypeAliasDeclaration(alias) = &declaration_record.data else {
                return Err(reject());
            };
            let literal = NodeRef::new(declaration.arena, declaration.file, alias.type_);
            let literal_record = host.node(literal).ok_or_else(reject)?;
            if declaration_record.kind != SyntaxKind::TypeAliasDeclaration
                || alias.type_parameters.is_some()
                || literal_record.parent != Some(declaration.node)
                || literal_record.kind != SyntaxKind::TypeLiteral
                || !host.symbol_matches(store, declaration, symbol)
            {
                return Err(reject());
            }
            plan_type_literal(store, host, literal, Some(symbol)).map_err(|_| reject())
        }
        _ => Err(reject()),
    }
}

fn declared_constructor_parameter_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<TypeId>, SourceNewError> {
    let record = host
        .node(node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidExpressionCache(node)))?;
    Ok(match record.kind {
        SyntaxKind::StringKeyword => Some(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
        SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
        _ => None,
    })
}

fn constructor_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    class: &ClassMemberQueryPlan,
) -> Result<Option<SourceNewParameter>, SourceNewError> {
    let Some(declaration) = class.constructor_declaration() else {
        return Ok(None);
    };
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(declaration));
    let constructor = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::ConstructorDeclaration(constructor_data) = &constructor.data else {
        return Err(invalid());
    };
    let parameter = match constructor_data.parameters.nodes.as_slice() {
        [] => return Ok(None),
        [parameter] => NodeRef::new(declaration.arena, declaration.file, *parameter),
        _ => return Err(unsupported(SourceNewUnsupported::Constructor(declaration))),
    };
    let parameter_record = host.node(parameter).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if parameter_data.type_.is_none() {
        let initializer = parameter_data
            .initializer
            .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
            .ok_or_else(invalid)?;
        let planned = plan_global_date_initializer(store, host, initializer)?;
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || host
                .node(initializer)
                .is_none_or(|record| record.parent != Some(parameter.node))
            || class.constructor_minimum_argument_count() != 0
            || planned.node() != initializer
            || class.constructor_parameter_symbols().len() != 1
        {
            return Err(invalid());
        }
        return Ok(None);
    }
    let type_node = parameter_data
        .type_
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
        .ok_or_else(invalid)?;
    let type_record = host.node(type_node).ok_or_else(invalid)?;
    let bound = host.bound_file(parameter).ok_or_else(invalid)?;
    let raw = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text))
        .ok_or_else(invalid)?;
    let symbol = store.get_merged_symbol(raw).ok_or_else(invalid)?;
    let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    if class.constructor_annotation() == Some(type_node) {
        if class.constructor_parameter_symbol() != Some(symbol)
            || class.type_query_context().is_none()
        {
            return Err(invalid());
        }
        return Ok(None);
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let type_ = match type_record.kind {
        SyntaxKind::AnyKeyword => bootstrap.any_type,
        SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
        SyntaxKind::StringKeyword => bootstrap.string_type,
        SyntaxKind::NumberKeyword => bootstrap.number_type,
        SyntaxKind::BigIntKeyword => bootstrap.bigint_type,
        SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
        SyntaxKind::SymbolKeyword => bootstrap.es_symbol_type,
        SyntaxKind::VoidKeyword => bootstrap.void_type,
        SyntaxKind::UndefinedKeyword => bootstrap.undefined_type,
        SyntaxKind::NeverKeyword => bootstrap.never_type,
        SyntaxKind::ObjectKeyword => bootstrap.non_primitive_type,
        _ => return Err(unsupported(SourceNewUnsupported::Constructor(parameter))),
    };
    if constructor.kind != SyntaxKind::Constructor
        || parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(declaration.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(parameter.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || type_record.parent != Some(parameter.node)
        || !matches!(type_record.data, NodeData::KeywordTypeNode(_))
        || raw != symbol
        || class.constructor_parameter_symbols() != [symbol]
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[parameter])
        || symbol_record.value_declaration() != Some(parameter)
    {
        return Err(invalid());
    }
    Ok(Some(SourceNewParameter { symbol, type_ }))
}

/// Resolves an imported constructor only after its normal alias binding exists.
fn imported_constructor_class(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    binding: &SourceImportBindingPlan,
) -> Result<ClassMemberQueryPlan, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let alias = store.symbol(binding.alias_symbol).ok_or_else(invalid)?;
    let links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(invalid)?;
    let AliasTargetState::Resolved(target) = links.alias_target else {
        return Err(invalid());
    };
    let target_record = store.symbol(target).ok_or_else(invalid)?;
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: plan.constructor,
            symbol: target,
        }));
    };
    let declaration = *declaration;
    let (_, bound) = host.source(declaration).ok_or_else(invalid)?;
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if binding.alias_symbol != plan.resolved_symbol
        || binding.declaration.file != plan.node.file
        || alias.flags() != SymbolFlags::ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.name().as_utf8() != Some(binding.local_text.as_str())
        || store.get_merged_symbol(binding.alias_symbol) != Some(binding.alias_symbol)
        || links.immediate_target.is_none()
        || links.type_only_declaration.is_some()
        || target_record.flags() != SymbolFlags::CLASS
        || target_record.check_flags() != CheckFlags::NONE
        || target_record.value_declaration() != Some(declaration)
        || store.get_merged_symbol(target) != Some(target)
        || declaration.file == plan.node.file
        || !facts.is_declaration_file()
        || !facts.is_external_module()
        || facts.is_common_js_module()
        || facts.is_javascript_file()
    {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: plan.constructor,
            symbol: target,
        }));
    }
    let class = plan_nongeneric_class_member_query(store, host, target)?;
    if class.symbol() != target
        || class.declaration() != declaration
        || class.export_local().is_none()
    {
        return Err(invariant(SourceNewInvariant::InvalidClassPlan(declaration)));
    }
    Ok(class)
}

fn imported_constructor_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
) -> Result<Option<SourceNewParameter>, SourceNewError> {
    if class.constructor_interface_annotation().is_some()
        || plan.argument.is_some() && class.direct_plan().is_none()
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
    }
    let parameter = constructor_parameter(store, host, class)?;
    if plan.argument.is_some() != parameter.is_some()
        || plan
            .argument
            .as_ref()
            .zip(parameter)
            .is_some_and(|(argument, parameter)| {
                !argument_matches_parameter(store, argument, parameter)
            })
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
    }
    Ok(parameter)
}

fn imported_constructor_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
) -> Result<Vec<TypeId>, SourceNewError> {
    let arity =
        preflight_class_or_interface_reference(store, host, class.symbol(), SymbolFlags::CLASS)?;
    if arity == 0 {
        if !plan.type_arguments.is_empty() {
            return Err(unsupported(SourceNewUnsupported::TypeArguments(plan.node)));
        }
        return Ok(Vec::new());
    }
    if !plan.type_arguments.is_empty() && plan.type_arguments.len() != arity {
        return Err(unsupported(SourceNewUnsupported::TypeArguments(plan.node)));
    }
    if plan.type_arguments.is_empty() {
        let unknown = store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.unknown_type)
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(class.declaration())))?;
        return Ok(vec![unknown; arity]);
    }
    Ok(plan
        .type_arguments
        .iter()
        .map(|argument| argument.type_)
        .collect())
}

fn argument_matches_parameter(
    store: &CanonicalTypeMapperStore,
    argument: &SourceNewArgument,
    parameter: SourceNewParameter,
) -> bool {
    store.intrinsic_bootstrap().is_some_and(|bootstrap| {
        let argument_type = match &argument.value {
            SourceNewArgumentValue::String(_) => bootstrap.string_type,
            SourceNewArgumentValue::Number(_) => bootstrap.number_type,
            SourceNewArgumentValue::Boolean(_) => bootstrap.boolean_type,
            SourceNewArgumentValue::EmptyObject(_) => bootstrap.empty_type_literal_type,
        };
        parameter.type_ == argument_type
            || parameter.type_ == bootstrap.any_type
            || parameter.type_ == bootstrap.unknown_type
    })
}

/// Revalidates the constructor provider and all observable construction caches.
pub(super) fn preflight_direct_default_new(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_direct_default_new_with_context(store, host, plan, None)
}

pub(super) fn preflight_direct_default_new_with_source_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_direct_default_new_with_context(store, host, plan, Some((globals, options)))
}

fn preflight_direct_default_new_with_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<(), SourceNewError> {
    if !plan.is_generic_source_class()
        && plan.expression_arguments.is_some()
        && !matches!(&plan.target, SourceNewTarget::SourceClass(class) if class.has_checked_constructor_arguments())
        && !matches!(&plan.target, SourceNewTarget::Class(_))
        && !(plan.is_library_constructor() && source_context.is_some())
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    for argument in plan.arguments() {
        if let SourceNewArgumentValue::EmptyObject(object) = &argument.value {
            let actual = plan_object_literal(store, host, argument.node).map_err(|_| {
                invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
            })?;
            if &actual != object.as_ref() {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    argument.node,
                )));
            }
            object_literal_state(store, object).map_err(|_| {
                invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
            })?;
        }
    }
    match &plan.target {
        SourceNewTarget::Library(_) | SourceNewTarget::GenericLibrary(_) => {
            let (globals, options) = source_context.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?;
            resolve_library_new_candidates(store, host, globals, options, plan)?;
        }
        SourceNewTarget::GenericSourceClass(generic) => {
            preflight_generic_source_class_plan(store, host, plan, generic)?;
        }
        SourceNewTarget::ConstructorOverloads(class) => {
            if super::classes::plan_source_constructor_overload_class(
                store,
                host,
                class.symbol(),
                class.type_query_context(),
            )?
            .as_ref()
                != Some(class.as_ref())
            {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                    class.declaration(),
                )));
            }
        }
        SourceNewTarget::SourceClass(class) => {
            resolved_source_class_constructor(store, host, plan, class)?;
        }
        SourceNewTarget::Class(class) => {
            preflight_nongeneric_class_member_query(store, host, class)?;
            if constructor_parameter(store, host, class)? != plan.parameter {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                    class.declaration(),
                )));
            }
            if plan.expression_arguments.is_some() {
                preflight_direct_class_expression_arguments(host, plan, class)?;
            }
        }
        SourceNewTarget::ImportedClass(binding) => {
            let class = imported_constructor_class(store, host, plan, binding)?;
            preflight_nongeneric_class_member_query(store, host, &class)?;
            imported_constructor_parameter(store, host, plan, &class)?;
            imported_constructor_type_arguments(store, host, plan, &class)?;
        }
        SourceNewTarget::Declared(expected) => {
            let (arena, bound) = host.source(plan.constructor).ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?;
            let actual = plan_declared_constructor(
                arena,
                bound,
                store,
                host,
                plan.node,
                plan.constructor,
                plan.resolved_symbol,
                plan.argument.as_ref(),
            )?;
            if actual != *expected || expected.parameter != plan.parameter {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::ClassUnion(expected) => {
            let (arena, bound) = host.source(plan.constructor).ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?;
            let mut prior_classes = HashMap::new();
            prior_classes
                .try_reserve(expected.classes.len())
                .map_err(|_| invariant(SourceNewInvariant::Capacity(plan.constructor)))?;
            for class in &expected.classes {
                let direct = class.direct_plan().ok_or_else(|| {
                    invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()))
                })?;
                if prior_classes
                    .insert(class.symbol(), direct.clone())
                    .is_some()
                {
                    return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                        plan.constructor,
                    )));
                }
            }
            let actual = match expected.provider {
                SourceClassUnionConstructorProvider::Ambient(_) => {
                    plan_declared_class_union_constructor(
                        arena,
                        bound,
                        store,
                        host,
                        &prior_classes,
                        plan.node,
                        plan.constructor,
                        plan.resolved_symbol,
                    )?
                }
                SourceClassUnionConstructorProvider::ArrayCallback { .. } => {
                    plan_callback_class_union_constructor(
                        arena,
                        bound,
                        store,
                        host,
                        &prior_classes,
                        plan.node,
                        plan.constructor,
                        plan.resolved_symbol,
                    )?
                    .ok_or_else(|| {
                        invariant(SourceNewInvariant::InvalidConstructorCache(
                            plan.constructor,
                        ))
                    })?
                }
            };
            if actual != *expected || plan.argument.is_some() || plan.parameter.is_some() {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::GlobalObject(expected) => {
            let actual = plan_global_object_constructor(
                store,
                host,
                plan.constructor,
                plan.resolved_symbol,
            )?;
            if actual != *expected
                || plan.parameter != plan.argument.as_ref().map(|_| expected.parameter)
            {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::GlobalArray(expected) => {
            let (arena, _) = host.source(plan.node).ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?;
            let actual = plan_global_array_constructor(
                arena,
                store,
                host,
                plan.node,
                plan.constructor,
                plan.resolved_symbol,
                plan.argument.as_ref(),
                &plan.additional_arguments,
            )?;
            if actual != *expected {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::GlobalDate(expected) => {
            let actual =
                plan_global_date_constructor(store, host, plan.constructor, plan.resolved_symbol)?;
            if actual != *expected || plan.argument.is_some() || plan.parameter.is_some() {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::DeclaredInterface(expected) => {
            let actual = global_error::plan(
                store,
                host,
                plan.constructor,
                plan.resolved_symbol,
                plan.argument.as_ref(),
            )?;
            if actual != *expected || plan.parameter != actual.parameter {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
        SourceNewTarget::GlobalPromise(expected) => {
            let actual = plan_global_promise_constructor(
                store,
                host,
                plan.constructor,
                plan.resolved_symbol,
                expected.executor,
            )?;
            if actual != *expected
                || plan.argument.is_some()
                || plan.parameter.is_some()
                || plan.executor.as_ref().is_none_or(|executor| {
                    executor.node != expected.executor
                        || !matches!(&executor.kind, PlannedExpressionKind::Arrow(_))
                })
            {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
        }
    }
    preflight_default_new_cache_with_context(store, host, plan, source_context)
}

/// Revalidates every construction, prepares required constructor signatures,
/// then reserves the use-site links. Expressions execute only after this
/// complete preparation batch succeeds.
#[allow(clippy::too_many_arguments)] // Preparation shares the source query's session and diagnostics.
pub(super) fn prepare_direct_default_news(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plans: &[SourceDefaultNewPlan],
) -> Result<(), SourceNewError> {
    let Some(capacity_node) = plans.first().map(|plan| plan.node) else {
        return Ok(());
    };
    let mut seen = HashSet::new();
    seen.try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    for plan in plans {
        if !seen.insert(plan.node) {
            return Err(invariant(SourceNewInvariant::DuplicatePlan(plan.node)));
        }
        preflight_direct_default_new_with_source_context(store, host, global_types, options, plan)?;
    }

    for plan in plans {
        for argument in plan.arguments() {
            if let SourceNewArgumentValue::EmptyObject(object) = &argument.value {
                publish_object_literal(store, object, &[]).map_err(|_| {
                    invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
                })?;
            }
        }
    }

    for plan in plans {
        match &plan.target {
            SourceNewTarget::Library(library)
            | SourceNewTarget::GenericLibrary(SourceGenericLibraryNewPlan { library, .. }) => {
                prepare_global_constructor_candidates(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    library,
                )
                .map_err(|error| {
                    trace_constructor_failure(
                        "provider_prepare",
                        plan.node,
                        plan.constructor,
                        format_args!("provider={:?} raw_error={error:?}", plan.resolved_symbol),
                    );
                    global_error::provider_error(plan.constructor, plan.resolved_symbol, error)
                })?;
                resolve_library_new_candidates(store, host, global_types, options, plan)?
                    .ok_or_else(|| {
                        invariant(SourceNewInvariant::InvalidConstructorCache(
                            plan.constructor,
                        ))
                    })?;
            }
            SourceNewTarget::ConstructorOverloads(class) => {
                super::classes::prepare_source_class_constructor_header(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    class,
                )?;
            }
            SourceNewTarget::DeclaredInterface(declared) => {
                global_error::prepare(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    plan,
                    declared,
                )?;
            }
            SourceNewTarget::GlobalObject(global)
                if resolved_global_object_constructor(store, plan, global)?.is_none() =>
            {
                materialize_global_object_constructor(store, host, plan, global)?;
            }
            SourceNewTarget::GlobalArray(global)
                if resolved_global_array_constructor(store, plan, global)?.is_none() =>
            {
                materialize_global_array_constructor(store, host, global_types, plan, global)?;
            }
            SourceNewTarget::GlobalDate(global)
                if resolved_global_date_constructor(store, plan, global)?.is_none() =>
            {
                materialize_global_date_constructor(store, host, plan, global)?;
            }
            SourceNewTarget::ImportedClass(binding) => {
                let class = imported_constructor_class(store, host, plan, binding)?;
                if !imported_constructor_type_arguments(store, host, plan, &class)?.is_empty() {
                    materialize_imported_generic_constructor(store, host, plan, &class)?;
                }
            }
            SourceNewTarget::GlobalPromise(global)
                if resolved_global_promise_constructor(store, plan, global)?.is_none() =>
            {
                materialize_global_promise_constructor(
                    store,
                    host,
                    global_types,
                    options,
                    plan,
                    global,
                )?;
            }
            _ => {}
        }
    }

    let mut strings = Vec::new();
    let mut numbers = Vec::new();
    strings
        .try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    numbers
        .try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    for argument in plans.iter().flat_map(SourceDefaultNewPlan::arguments) {
        match &argument.value {
            SourceNewArgumentValue::String(value) => strings.push(value.clone()),
            SourceNewArgumentValue::Number(value) => numbers.push(*value),
            SourceNewArgumentValue::Boolean(_) | SourceNewArgumentValue::EmptyObject(_) => {}
        }
    }
    if !strings.is_empty() || !numbers.is_empty() {
        store
            .prepare_regular_literal_types(&strings, &numbers, &[])
            .map_err(|error| literal_cache_error(capacity_node, error))?;
    }

    let mut symbol_nodes = 0usize;
    let mut constructor_type_nodes = 0usize;
    let mut expression_type_nodes = 0usize;
    let mut argument_type_nodes = 0usize;
    let mut signatures = 0usize;
    for plan in plans {
        symbol_nodes = symbol_nodes
            .checked_add(usize::from(
                store.symbol_node_links(plan.constructor).is_none(),
            ))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        constructor_type_nodes = constructor_type_nodes
            .checked_add(usize::from(
                store.type_node_links(plan.constructor).is_none(),
            ))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        expression_type_nodes = expression_type_nodes
            .checked_add(usize::from(store.type_node_links(plan.node).is_none()))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        for argument in plan.arguments() {
            argument_type_nodes = argument_type_nodes
                .checked_add(usize::from(store.type_node_links(argument.node).is_none()))
                .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        }
        for argument in &plan.type_arguments {
            argument_type_nodes = argument_type_nodes
                .checked_add(usize::from(store.type_node_links(argument.node).is_none()))
                .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        }
        for &argument in plan.written_type_argument_nodes().unwrap_or_default() {
            argument_type_nodes = argument_type_nodes
                .checked_add(usize::from(store.type_node_links(argument).is_none()))
                .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        }
        signatures = signatures
            .checked_add(usize::from(store.signature_links(plan.node).is_none()))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
    }
    let type_nodes = constructor_type_nodes
        .checked_add(expression_type_nodes)
        .and_then(|count| count.checked_add(argument_type_nodes))
        .ok_or_else(|| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    let symbol_capacity = store.try_reserve_symbol_node_links(symbol_nodes);
    let type_capacity = store.try_reserve_type_node_links(type_nodes);
    let signature_capacity = store.try_reserve_signature_links(signatures);
    if !(symbol_capacity && type_capacity && signature_capacity) {
        return Err(invariant(SourceNewInvariant::Capacity(capacity_node)));
    }

    for plan in plans {
        if store.symbol_node_links(plan.constructor).is_none() {
            assert!(store.ensure_symbol_node_links(plan.constructor));
        }
        if store.type_node_links(plan.constructor).is_none() {
            assert!(store.ensure_type_node_links(plan.constructor));
        }
        if store.signature_links(plan.node).is_none() {
            assert!(store.ensure_signature_links(plan.node));
        }
        if store.type_node_links(plan.node).is_none() {
            assert!(store.ensure_type_node_links(plan.node));
        }
        for argument in plan.arguments() {
            if store.type_node_links(argument.node).is_none() {
                assert!(store.ensure_type_node_links(argument.node));
            }
        }
        for argument in &plan.type_arguments {
            if store.type_node_links(argument.node).is_none() {
                assert!(store.ensure_type_node_links(argument.node));
            }
        }
        for &argument in plan.written_type_argument_nodes().unwrap_or_default() {
            if store.type_node_links(argument).is_none() {
                assert!(store.ensure_type_node_links(argument));
            }
        }
    }
    Ok(())
}

fn resolved_imported_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let instance = store
        .declared_type_links(class.symbol())
        .and_then(|links| links.declared_type);
    let value = exact_class_value_type(store, class.symbol())?;
    let (Some(instance_type), Some(value_type)) = (instance, value) else {
        if value.is_some() {
            return Err(invalid());
        }
        return Ok(None);
    };
    let value_record = store.type_payload(value_type).ok_or_else(invalid)?;
    let Some([base_signature]) = value_record
        .data()
        .structured()
        .and_then(|structured| structured.signatures.as_deref())
    else {
        return Err(invalid());
    };
    let base_signature = *base_signature;
    validate_selected_default_signature(
        store,
        host,
        plan,
        class,
        value_type,
        instance_type,
        base_signature,
    )?;
    let type_arguments = imported_constructor_type_arguments(store, host, plan, class)?;
    if type_arguments.is_empty() {
        return Ok(Some(CheckedSourceDefaultNew {
            value_type,
            instance_type,
            signature: base_signature,
        }));
    }

    let instance_record = store.type_payload(instance_type).ok_or_else(invalid)?;
    let TypeData::Interface(origin) = instance_record.data() else {
        return Err(invalid());
    };
    let Some(type_parameters) = origin.reference.resolved_type_arguments.as_deref() else {
        return Err(invalid());
    };
    let TypeCacheState::Allocated(instantiations) = &origin.reference.object.instantiations else {
        return Err(invalid());
    };
    let key = type_list_key(&type_arguments);
    let instantiated_type = instantiations.get(&key).copied();
    let signature = match store.cached_signature(base_signature, key, &type_arguments) {
        CachedSignatureLookup::Hit(signature) => signature,
        CachedSignatureLookup::Missing => return Ok(None),
        CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
            return Err(invalid());
        }
    };
    let instantiated_type = instantiated_type.ok_or_else(invalid)?;
    let instance_record = store.type_payload(instantiated_type).ok_or_else(invalid)?;
    let TypeData::TypeReference(reference) = instance_record.data() else {
        return Err(invalid());
    };
    let selected = store.signature(signature).ok_or_else(invalid)?;
    let parameter = imported_constructor_parameter(store, host, plan, class)?;
    if reference.object.target != Some(instance_type)
        || reference.resolved_type_arguments.as_deref() != Some(type_arguments.as_slice())
        || selected.flags() != SignatureFlags::CONSTRUCT
        || selected.declaration() != class.constructor_declaration()
        || !selected.type_parameters().is_empty()
        || selected.parameters() != parameter.map(|parameter| parameter.symbol).as_slice()
        || selected.min_argument_count() != i32::from(parameter.is_some())
        || selected.resolved_return_type() != Some(instantiated_type)
        || selected.target() != Some(base_signature)
        || selected.mapper().is_none_or(|mapper| {
            store.type_mapper_has_exact_endpoints(mapper, type_parameters, &type_arguments)
                != Some(true)
        })
    {
        return Err(invalid());
    }
    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type: instantiated_type,
        signature,
    }))
}

fn materialize_imported_generic_constructor(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
) -> Result<(), SourceNewError> {
    if resolved_imported_constructor(store, host, plan, class)?.is_some() {
        return Ok(());
    }
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let members = execute_nongeneric_class_member_query(store, host, class)?;
    let target = members.shells().instance_type();
    let base = members.default_construct_signature();
    let type_parameters = match store
        .type_payload(target)
        .map(super::type_records::TypeRecord::data)
    {
        Some(TypeData::Interface(interface)) => interface
            .reference
            .resolved_type_arguments
            .clone()
            .ok_or_else(invalid)?,
        _ => return Err(invalid()),
    };
    let type_arguments = imported_constructor_type_arguments(store, host, plan, class)?;
    if type_parameters.is_empty() || type_parameters.len() != type_arguments.len() {
        return Err(invalid());
    }
    let key = type_list_key(&type_arguments);
    match store.cached_signature(base, key, &type_arguments) {
        CachedSignatureLookup::Hit(_) => return Err(invalid()),
        CachedSignatureLookup::Missing => {}
        CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
            return Err(invalid());
        }
    }
    if !store.try_reserve_mappers(1) || !store.try_reserve_cached_signatures(1) {
        return Err(invariant(SourceNewInvariant::Capacity(plan.node)));
    }
    let instance = store
        .create_direct_generic_reference_type(target, &type_arguments)
        .map_err(|_| invalid())?;
    let mapper = store
        .new_type_mapper(type_parameters, type_arguments.clone())
        .ok_or_else(invalid)?;
    let signature = store
        .instantiate_signature_ex(base, mapper, true)
        .map_err(|_| invalid())?;
    if !store.set_signature_resolved_return_type(signature, Some(instance))
        || !store.set_cached_signature(base, key, type_arguments.into_boxed_slice(), signature)
    {
        return Err(invalid());
    }
    if resolved_imported_constructor(store, host, plan, class)?.is_none() {
        return Err(invalid());
    }
    Ok(())
}

/// Publishes a bound Object or Boolean constructor without resolving other members.
fn materialize_global_object_constructor(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalObjectConstructorPlan,
) -> Result<(), SourceNewError> {
    if resolved_global_object_constructor(store, plan, global)?.is_some() {
        return Ok(());
    }

    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let declared = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type);
    let annotation = exact_type_cache(store, global.annotation).map_err(|()| invalid())?;
    let annotation_symbol = exact_symbol_cache(store, global.annotation).map_err(|()| invalid())?;
    let object_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let parameter = exact_class_value_type(store, global.parameter.symbol)?;
    let signature = exact_signature_cache(store, global.declaration).map_err(|()| invalid())?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    let return_symbol =
        exact_symbol_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if signature.is_some()
        || annotation.is_some_and(|type_| Some(type_) != declared)
        || annotation_symbol.is_some_and(|symbol| symbol != global.owner)
        || object_value.is_some_and(|type_| Some(type_) != declared)
        || parameter.is_some_and(|type_| type_ != global.parameter.type_)
        || return_annotation.is_some_and(|type_| type_ != global.object_type)
        || return_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
    {
        return Err(invalid());
    }
    if let Some(type_) = declared {
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Interface(interface) = record.data() else {
            return Err(invalid());
        };
        if record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            || interface.declared_members_resolved
            || interface.reference.object.structured.signatures.is_some()
            || interface.declared_construct_signatures.is_some()
        {
            return Err(invalid());
        }
    }

    let missing_type_nodes = usize::from(store.type_node_links(global.annotation).is_none())
        + usize::from(store.type_node_links(global.return_annotation).is_none());
    let missing_symbol_nodes = usize::from(store.symbol_node_links(global.annotation).is_none())
        + usize::from(store.symbol_node_links(global.return_annotation).is_none());
    let missing_value_symbols =
        usize::from(store.value_symbol_links(plan.resolved_symbol).is_none())
            + usize::from(store.value_symbol_links(global.parameter.symbol).is_none());
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(global.declaration).is_none(),
        ))
        || !store.try_reserve_type_node_links(missing_type_nodes)
        || !store.try_reserve_symbol_node_links(missing_symbol_nodes)
        || !store.try_reserve_value_symbol_links(missing_value_symbols)
        || !store.try_reserve_function_signature_return_annotations(1)
    {
        return Err(invariant(SourceNewInvariant::Capacity(plan.constructor)));
    }

    let value_type = store.get_declared_type_of_symbol(host, global.owner)?;
    if declared.is_some_and(|declared| declared != value_type) {
        return Err(invalid());
    }
    let value_record = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value_record.data() else {
        return Err(invalid());
    };
    if value_record.flags() != TypeFlags::OBJECT
        || !value_record.object_flags().contains(ObjectFlags::INTERFACE)
        || value_record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        || value_record.symbol() != Some(global.owner)
        || value_record.alias().is_some()
        || interface.declared_members_resolved
        || interface.reference.object.structured.signatures.is_some()
        || interface.declared_construct_signatures.is_some()
    {
        return Err(invalid());
    }

    let signature = store
        .alloc_signature(
            SignatureFlags::CONSTRUCT,
            Some(global.declaration),
            Vec::new(),
            None,
            vec![global.parameter.symbol],
            Some(global.object_type),
            None,
            0,
        )
        .expect("the authenticated global constructor reserved its bound signature");
    assert!(store.set_type_node_links(
        global.annotation,
        TypeNodeLinks {
            resolved_type: Some(value_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_symbol_node_links(
        global.annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(global.owner),
        },
    ));
    assert!(store.set_type_node_links(
        global.return_annotation,
        TypeNodeLinks {
            resolved_type: Some(global.object_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_symbol_node_links(
        global.return_annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(plan.resolved_symbol),
        },
    ));
    assert!(store.set_value_symbol_links(
        plan.resolved_symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_value_symbol_links(
        global.parameter.symbol,
        ValueSymbolLinks {
            resolved_type: Some(global.parameter.type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_signature_links(
        global.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(store.set_function_signature_return_annotation(
        signature,
        global.return_annotation,
        false,
    ));
    debug_assert_eq!(
        resolved_global_object_constructor(store, plan, global),
        Ok(Some(CheckedSourceDefaultNew {
            value_type,
            instance_type: global.object_type,
            signature,
        })),
    );
    Ok(())
}

/// Publishes the real zero-argument Date signature without resolving members.
fn materialize_global_date_constructor(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalDateConstructorPlan,
) -> Result<(), SourceNewError> {
    if resolved_global_date_constructor(store, plan, global)?.is_some() {
        return Ok(());
    }

    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let date_type = store
        .declared_type_links(plan.resolved_symbol)
        .and_then(|links| links.declared_type);
    let declared = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type);
    let annotation = exact_type_cache(store, global.annotation).map_err(|()| invalid())?;
    let annotation_symbol = exact_symbol_cache(store, global.annotation).map_err(|()| invalid())?;
    let date_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let signature = exact_signature_cache(store, global.declaration).map_err(|()| invalid())?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    let return_symbol =
        exact_symbol_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if signature.is_some()
        || annotation.is_some_and(|type_| Some(type_) != declared)
        || annotation_symbol.is_some_and(|symbol| symbol != global.owner)
        || date_value.is_some_and(|type_| Some(type_) != declared)
        || return_annotation.is_some_and(|type_| Some(type_) != date_type)
        || return_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
    {
        return Err(invalid());
    }
    if let Some(type_) = declared {
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Interface(interface) = record.data() else {
            return Err(invalid());
        };
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
            || record.symbol() != Some(global.owner)
            || record.alias().is_some()
            || interface.declared_members_resolved
            || interface.reference.object.structured.signatures.is_some()
            || interface.declared_construct_signatures.is_some()
        {
            return Err(invalid());
        }
    }
    for symbol in [plan.resolved_symbol, global.owner] {
        let flags = store.symbol(symbol).ok_or_else(invalid)?.flags();
        if preflight_class_or_interface_reference(store, host, symbol, flags)? != 0 {
            return Err(invalid());
        }
    }

    let missing_type_nodes = usize::from(store.type_node_links(global.annotation).is_none())
        + usize::from(store.type_node_links(global.return_annotation).is_none());
    let missing_symbol_nodes = usize::from(store.symbol_node_links(global.annotation).is_none())
        + usize::from(store.symbol_node_links(global.return_annotation).is_none());
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(global.declaration).is_none(),
        ))
        || !store.try_reserve_type_node_links(missing_type_nodes)
        || !store.try_reserve_symbol_node_links(missing_symbol_nodes)
        || !store.try_reserve_value_symbol_links(usize::from(
            store.value_symbol_links(plan.resolved_symbol).is_none(),
        ))
        || !store.try_reserve_function_signature_return_annotations(1)
    {
        return Err(invariant(SourceNewInvariant::Capacity(plan.constructor)));
    }

    let instance_type = store.get_declared_type_of_symbol(host, plan.resolved_symbol)?;
    if date_type.is_some_and(|declared| declared != instance_type) {
        return Err(invalid());
    }
    let instance = store.type_payload(instance_type).ok_or_else(invalid)?;
    if instance.flags() != TypeFlags::OBJECT
        || !instance.object_flags().contains(ObjectFlags::INTERFACE)
        || instance.symbol() != Some(plan.resolved_symbol)
        || instance.alias().is_some()
    {
        return Err(invalid());
    }

    let value_type = store.get_declared_type_of_symbol(host, global.owner)?;
    if declared.is_some_and(|declared| declared != value_type) {
        return Err(invalid());
    }
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value.data() else {
        return Err(invalid());
    };
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || interface.declared_members_resolved
        || interface.reference.object.structured.signatures.is_some()
        || interface.declared_construct_signatures.is_some()
    {
        return Err(invalid());
    }

    let signature = store
        .alloc_signature(
            SignatureFlags::CONSTRUCT,
            Some(global.declaration),
            Vec::new(),
            None,
            Vec::new(),
            Some(instance_type),
            None,
            0,
        )
        .expect("the authenticated Date constructor reserved its bound signature");
    assert!(store.set_type_node_links(
        global.annotation,
        TypeNodeLinks {
            resolved_type: Some(value_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_symbol_node_links(
        global.annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(global.owner),
        },
    ));
    assert!(store.set_type_node_links(
        global.return_annotation,
        TypeNodeLinks {
            resolved_type: Some(instance_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_symbol_node_links(
        global.return_annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(plan.resolved_symbol),
        },
    ));
    assert!(store.set_value_symbol_links(
        plan.resolved_symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_signature_links(
        global.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(store.set_function_signature_return_annotation(
        signature,
        global.return_annotation,
        false,
    ));
    debug_assert_eq!(
        resolved_global_date_constructor(store, plan, global),
        Ok(Some(CheckedSourceDefaultNew {
            value_type,
            instance_type,
            signature,
        })),
    );
    Ok(())
}

/// Materializes the real generic Promise constructor and its lazy executor types.
#[allow(clippy::too_many_arguments)] // Preserve the constructor's production query options.
fn materialize_global_promise_constructor(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalPromiseConstructorPlan,
) -> Result<(), SourceNewError> {
    if resolved_global_promise_constructor(store, plan, global)?.is_some() {
        return Ok(());
    }
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let owner_flags = store.symbol(global.owner).ok_or_else(invalid)?.flags();
    let promise_flags = store
        .symbol(plan.resolved_symbol)
        .ok_or_else(invalid)?
        .flags();
    if preflight_class_or_interface_reference(store, host, global.owner, owner_flags)? != 0
        || preflight_class_or_interface_reference(store, host, plan.resolved_symbol, promise_flags)?
            != 1
    {
        return Err(invalid());
    }
    let declared_owner = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type);
    if exact_type_cache(store, global.annotation)
        .map_err(|()| invalid())?
        .is_some_and(|cached| Some(cached) != declared_owner)
        || exact_class_value_type(store, plan.resolved_symbol)?
            .is_some_and(|cached| Some(cached) != declared_owner)
    {
        return Err(invalid());
    }

    let promise_target = store.get_declared_type_of_symbol(host, plan.resolved_symbol)?;
    let reference =
        validate_direct_generic_reference(store, promise_target).map_err(|_| invalid())?;
    if reference.target != promise_target || reference.type_arguments.len() != 1 {
        return Err(invalid());
    }
    let value_type = store.get_declared_type_of_symbol(host, global.owner)?;
    if declared_owner.is_some_and(|declared| declared != value_type) {
        return Err(invalid());
    }
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value.data() else {
        return Err(invalid());
    };
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || interface.declared_members_resolved
        || interface.reference.object.structured.signatures.is_some()
        || interface.declared_construct_signatures.is_some()
    {
        return Err(invalid());
    }

    let generic = execute_type_parameter(store, global.type_parameter);
    let mut query_diagnostics = CanonicalCheckerDiagnostics::default();
    let (executor_type, return_type) = {
        let mut query = CanonicalTypeQuery::new_with_global_types(
            store,
            host,
            global_types,
            options,
            &mut query_diagnostics,
        )?;
        (
            query.get_type_from_type_node(global.parameter_annotation)?,
            query.get_type_from_type_node(global.return_annotation)?,
        )
    };
    if !query_diagnostics.is_empty() {
        return Err(invalid());
    }
    let expected_return =
        create_direct_generic_reference(store, promise_target, &[generic], ObjectFlags::NONE)
            .map_err(|_| invalid())?;
    if return_type != expected_return {
        return Err(invalid());
    }
    let unknown = store
        .intrinsic_bootstrap()
        .ok_or_else(invalid)?
        .unknown_type;
    let instance_type =
        create_direct_generic_reference(store, promise_target, &[unknown], ObjectFlags::NONE)
            .map_err(|_| invalid())?;

    let base = if let Some(signature) =
        exact_signature_cache(store, global.declaration).map_err(|()| invalid())?
    {
        let record = store.signature(signature).ok_or_else(invalid)?;
        if record.declaration() != Some(global.declaration)
            || record.flags() != SignatureFlags::CONSTRUCT
            || record.type_parameters() != [generic]
            || record.parameters() != [global.parameter]
            || record.min_argument_count() != 1
            || record.resolved_return_type() != Some(return_type)
        {
            return Err(invalid());
        }
        signature
    } else {
        if exact_class_value_type(store, global.parameter)?
            .is_some_and(|cached| cached != executor_type)
            || !store.try_reserve_signatures(1)
            || !store.try_reserve_signature_links(usize::from(
                store.signature_links(global.declaration).is_none(),
            ))
            || !store.try_reserve_type_node_links(usize::from(
                store.type_node_links(global.annotation).is_none(),
            ))
            || !store.try_reserve_value_symbol_links(
                usize::from(store.value_symbol_links(plan.resolved_symbol).is_none())
                    + usize::from(store.value_symbol_links(global.parameter).is_none()),
            )
            || !store.try_reserve_function_signature_return_annotations(1)
        {
            return Err(invalid());
        }
        let signature = store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                Some(global.declaration),
                vec![generic],
                None,
                vec![global.parameter],
                Some(return_type),
                None,
                1,
            )
            .ok_or_else(invalid)?;
        assert!(store.set_type_node_links(
            global.annotation,
            TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            plan.resolved_symbol,
            ValueSymbolLinks {
                resolved_type: Some(value_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            global.parameter,
            ValueSymbolLinks {
                resolved_type: Some(executor_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_signature_links(
            global.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_function_signature_return_annotation(
            signature,
            global.return_annotation,
            false,
        ));
        signature
    };

    let key = type_list_key(&[unknown]);
    match store.cached_signature(base, key, &[unknown]) {
        CachedSignatureLookup::Hit(signature) => {
            if store
                .signature(signature)
                .and_then(super::signatures::Signature::resolved_return_type)
                != Some(instance_type)
            {
                return Err(invalid());
            }
        }
        CachedSignatureLookup::Missing => {
            let mapper = store
                .new_simple_type_mapper(generic, unknown)
                .ok_or_else(invalid)?;
            let signature = store
                .instantiate_signature_ex(base, mapper, true)
                .map_err(|_| invalid())?;
            if !store.try_reserve_cached_signatures(1)
                || !store.set_signature_resolved_return_type(signature, Some(instance_type))
                || !store.set_cached_signature(base, key, Box::new([unknown]), signature)
            {
                return Err(invalid());
            }
        }
        CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
            return Err(invalid());
        }
    }

    if resolved_global_promise_constructor(store, plan, global)?.is_none() {
        return Err(invalid());
    }
    Ok(())
}

/// Publishes only the selected real `ArrayConstructor` declaration and instance.
fn materialize_global_array_constructor(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalArrayConstructorPlan,
) -> Result<(), SourceNewError> {
    if resolved_global_array_constructor(store, plan, global)?.is_some() {
        return Ok(());
    }
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    if global_types.array_type != global.array_target {
        return Err(invalid());
    }
    let value_type = store.get_declared_type_of_symbol(host, global.owner)?;
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value.data() else {
        return Err(invalid());
    };
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || interface.reference.object.structured.signatures.is_some()
        || exact_type_cache(store, global.annotation)
            .map_err(|()| invalid())?
            .is_some_and(|annotation| annotation != value_type)
        || exact_class_value_type(store, plan.resolved_symbol)?
            .is_some_and(|value| value != value_type)
    {
        return Err(invalid());
    }

    let selected = match global.selection {
        SourceGlobalArraySelection::Length => global.length,
        SourceGlobalArraySelection::GenericLength(_) => global.generic_length,
        SourceGlobalArraySelection::Items(_) => global.items,
    };
    let base = if let Some(signature) =
        exact_signature_cache(store, selected.declaration).map_err(|()| invalid())?
    {
        signature
    } else {
        let type_parameter = selected
            .type_parameter
            .map(|parameter| execute_type_parameter(store, parameter));
        let parameter_type = match global.selection {
            SourceGlobalArraySelection::Items(_) => store
                .create_canonical_array_type(
                    global_types,
                    type_parameter.ok_or_else(invalid)?,
                    false,
                )
                .map_err(|_| invalid())?,
            SourceGlobalArraySelection::Length | SourceGlobalArraySelection::GenericLength(_) => {
                store.intrinsic_bootstrap().ok_or_else(invalid)?.number_type
            }
        };
        let return_type = match type_parameter {
            Some(parameter) => store
                .create_canonical_array_type(global_types, parameter, false)
                .map_err(|_| invalid())?,
            None => global_types.any_array_type,
        };
        let missing_type_nodes = [
            global.annotation,
            selected.parameter_annotation,
            selected.return_annotation,
        ]
        .iter()
        .filter(|node| store.type_node_links(**node).is_none())
        .count();
        let missing_values = [plan.resolved_symbol, selected.parameter]
            .iter()
            .filter(|symbol| store.value_symbol_links(**symbol).is_none())
            .count();
        if !store.try_reserve_signatures(1)
            || !store.try_reserve_signature_links(usize::from(
                store.signature_links(selected.declaration).is_none(),
            ))
            || !store.try_reserve_type_node_links(missing_type_nodes)
            || !store.try_reserve_value_symbol_links(missing_values)
            || !store.try_reserve_function_signature_return_annotations(1)
        {
            return Err(invariant(SourceNewInvariant::Capacity(plan.constructor)));
        }
        if store
            .value_symbol_links(selected.parameter)
            .is_some_and(|links| {
                links != &ValueSymbolLinks::default()
                    && links
                        != &ValueSymbolLinks {
                            resolved_type: Some(parameter_type),
                            ..ValueSymbolLinks::default()
                        }
            })
            || exact_type_cache(store, selected.parameter_annotation)
                .map_err(|()| invalid())?
                .is_some_and(|cached| cached != parameter_type)
            || exact_type_cache(store, selected.return_annotation)
                .map_err(|()| invalid())?
                .is_some_and(|cached| cached != return_type)
        {
            return Err(invalid());
        }
        let flags = SignatureFlags::CONSTRUCT
            | if matches!(global.selection, SourceGlobalArraySelection::Items(_)) {
                SignatureFlags::HAS_REST_PARAMETER
            } else {
                SignatureFlags::NONE
            };
        let minimum = i32::from(matches!(
            global.selection,
            SourceGlobalArraySelection::GenericLength(_)
        ));
        let signature = store
            .alloc_signature(
                flags,
                Some(selected.declaration),
                type_parameter.into_iter().collect(),
                None,
                vec![selected.parameter],
                Some(return_type),
                None,
                minimum,
            )
            .ok_or_else(invalid)?;
        assert!(store.set_type_node_links(
            global.annotation,
            TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_type_node_links(
            selected.parameter_annotation,
            TypeNodeLinks {
                resolved_type: Some(parameter_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_type_node_links(
            selected.return_annotation,
            TypeNodeLinks {
                resolved_type: Some(return_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            plan.resolved_symbol,
            ValueSymbolLinks {
                resolved_type: Some(value_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            selected.parameter,
            ValueSymbolLinks {
                resolved_type: Some(parameter_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_signature_links(
            selected.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_function_signature_return_annotation(
            signature,
            selected.return_annotation,
            false,
        ));
        signature
    };

    if let SourceGlobalArraySelection::GenericLength(element)
    | SourceGlobalArraySelection::Items(element) = global.selection
    {
        let key = type_list_key(&[element]);
        match store.cached_signature(base, key, &[element]) {
            CachedSignatureLookup::Hit(_) => {}
            CachedSignatureLookup::Missing => {
                let generic = store
                    .signature(base)
                    .and_then(|signature| signature.type_parameters().first())
                    .copied()
                    .ok_or_else(invalid)?;
                let mapper = store
                    .new_simple_type_mapper(generic, element)
                    .ok_or_else(invalid)?;
                let signature = store
                    .instantiate_signature_ex(base, mapper, true)
                    .map_err(|_| invalid())?;
                let return_type = store
                    .create_canonical_array_type(global_types, element, false)
                    .map_err(|_| invalid())?;
                if !store.try_reserve_cached_signatures(1)
                    || !store.set_signature_resolved_return_type(signature, Some(return_type))
                    || !store.set_cached_signature(base, key, Box::new([element]), signature)
                {
                    return Err(invalid());
                }
            }
            CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
                return Err(invalid());
            }
        }
    }

    if resolved_global_array_constructor(store, plan, global)?.is_none() {
        return Err(invalid());
    }
    Ok(())
}

/// Selects the exact default construct signature and publishes the constructor,
/// signature, and result caches as one prevalidated suffix.
pub(super) fn check_direct_default_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    if plan.expression_arguments.is_some() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    preflight_direct_default_new(store, host, plan)?;
    preflight_prepared_default_new_cache(store, host, plan)?;
    let selected = match &plan.target {
        SourceNewTarget::Library(_) | SourceNewTarget::GenericLibrary(_) => {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                plan.node,
            )));
        }
        SourceNewTarget::ConstructorOverloads(_) | SourceNewTarget::GenericSourceClass(_) => {
            return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
        }
        SourceNewTarget::SourceClass(class) => {
            resolved_source_class_constructor(store, host, plan, class)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::Class(class) => {
            let members = execute_nongeneric_class_member_query(store, host, class)?;
            let selected = CheckedSourceDefaultNew {
                value_type: members.shells().value_type(),
                instance_type: members.shells().instance_type(),
                signature: members.default_construct_signature(),
            };
            validate_selected_default_signature(
                store,
                host,
                plan,
                class,
                selected.value_type,
                selected.instance_type,
                selected.signature,
            )?;
            selected
        }
        SourceNewTarget::ImportedClass(binding) => {
            let class = imported_constructor_class(store, host, plan, binding)?;
            execute_nongeneric_class_member_query(store, host, &class)?;
            resolved_imported_constructor(store, host, plan, &class)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::Declared(declared) => {
            resolved_declared_constructor(store, plan, declared)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::ClassUnion(union) => {
            materialize_class_union_constructor(store, plan, union)?
        }
        SourceNewTarget::GlobalObject(global) => {
            resolved_global_object_constructor(store, plan, global)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::GlobalArray(global) => {
            resolved_global_array_constructor(store, plan, global)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::GlobalDate(global) => {
            resolved_global_date_constructor(store, plan, global)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::DeclaredInterface(declared) => {
            global_error::resolve(store, host, plan, declared)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
        SourceNewTarget::GlobalPromise(global) => {
            resolved_global_promise_constructor(store, plan, global)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
        }
    };
    publish_checked_default_new(store, host, plan, selected)
}

fn publish_checked_default_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    selected: CheckedSourceDefaultNew,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    let argument_types = materialize_new_argument_types(store, plan)?;
    publish_default_new_links(store, host, plan, selected, &argument_types)
}

/// A selected public constructor and a note from its checked hidden implementation.
pub(super) struct CheckedSourceConstructorOverloadNew {
    pub(super) checked: CheckedSourceDefaultNew,
    pub(super) resolution: super::calls::DirectCallResolution,
    pub(super) implementation_note: Option<NodeRef>,
}

pub(super) fn check_source_constructor_overload_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    plan: &SourceDefaultNewPlan,
    session: &mut InstantiationSession,
) -> Result<Option<CheckedSourceConstructorOverloadNew>, SourceNewError> {
    let SourceNewTarget::ConstructorOverloads(class) = &plan.target else {
        return Ok(None);
    };
    preflight_direct_default_new(store, host, plan)?;
    preflight_prepared_default_new_cache(store, host, plan)?;
    let existing_signature = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let group = super::classes::source_class_constructor_overloads(store, host, class.symbol())?
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(class.declaration())))?;
    let arguments = materialize_new_argument_types(store, plan)?;
    let value_type = group.members.shells().value_type();
    let instance_type = group.members.shells().instance_type();
    if group.signatures.iter().any(|signature| {
        signature.owner != value_type
            || signature.return_type != Some(instance_type)
            || store
                .signature(signature.signature)
                .is_none_or(|record| !record.flags().contains(SignatureFlags::CONSTRUCT))
    }) {
        return Err(invariant(SourceNewInvariant::InvalidClassPlan(
            class.declaration(),
        )));
    }
    let request = super::calls::DirectCallRequest {
        form: super::calls::DirectCallForm::New,
        callee: value_type,
        arguments: &arguments,
        optional_chain: false,
        type_argument_count: 0,
        has_spread_argument: false,
    };
    let resolution = super::calls::resolve_direct_call_candidates_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        &group.signatures,
        existing_signature,
        session,
    )
    .map_err(|error| SourceNewError::Call {
        node: plan.node,
        error,
    })?;
    if resolution.projection.return_type != instance_type {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    let implementation_note = if matches!(
        resolution.applicability,
        super::calls::DirectCallApplicability::ArgumentNotAssignable { .. }
    ) && super::calls::class_overload_implementation_accepts_arguments(
        store,
        global_types,
        strict_function_types,
        request,
        &group.implementation,
        session,
    )
    .map_err(|error| SourceNewError::Call {
        node: plan.node,
        error,
    })? {
        Some(
            store
                .signature(group.implementation.signature)
                .and_then(Signature::declaration)
                .ok_or_else(|| {
                    invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()))
                })?,
        )
    } else {
        None
    };
    let selected = CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature: resolution.projection.signature,
    };
    let checked = publish_default_new_links(store, host, plan, selected, &arguments)?;
    Ok(Some(CheckedSourceConstructorOverloadNew {
        checked,
        resolution,
        implementation_note,
    }))
}

fn materialize_new_argument_types(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
) -> Result<Vec<TypeId>, SourceNewError> {
    plan.arguments()
        .map(|argument| {
            let regular = match &argument.value {
                SourceNewArgumentValue::String(value) => {
                    store.regular_string_literal_type(value.clone())
                }
                SourceNewArgumentValue::Number(value) => store.regular_number_literal_type(*value),
                SourceNewArgumentValue::Boolean(value) => {
                    return store
                        .intrinsic_bootstrap()
                        .map(|bootstrap| {
                            if *value {
                                bootstrap.true_type
                            } else {
                                bootstrap.false_type
                            }
                        })
                        .ok_or_else(|| {
                            invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
                        });
                }
                SourceNewArgumentValue::EmptyObject(object) => {
                    return object_literal_state(store, object)
                        .map_err(|_| {
                            invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
                        })?
                        .filter(|state| state.is_resolved())
                        .map(PropertyObjectState::type_id)
                        .ok_or_else(|| {
                            invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
                        });
                }
            }
            .map_err(|error| literal_cache_error(argument.node, error))?;
            store
                .fresh_type_of_literal_type(regular)
                .map_err(|error| literal_cache_error(argument.node, error))
        })
        .collect::<Result<Vec<_>, _>>()
}

fn publish_default_new_links(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    selected: CheckedSourceDefaultNew,
    argument_types: &[TypeId],
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    publish_default_new_links_with_context(store, host, plan, selected, argument_types, None)
}

fn publish_default_new_links_with_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    selected: CheckedSourceDefaultNew,
    argument_types: &[TypeId],
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    let CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    } = selected;
    preflight_publication_cache_with_context(
        store,
        host,
        plan,
        value_type,
        instance_type,
        signature,
        argument_types,
        source_context,
    )?;

    let symbol_links = SymbolNodeLinks {
        resolved_symbol: Some(plan.resolved_symbol),
    };
    let constructor_links = TypeNodeLinks {
        resolved_type: Some(value_type),
        ..TypeNodeLinks::default()
    };
    let expression_links = TypeNodeLinks {
        resolved_type: Some(instance_type),
        ..TypeNodeLinks::default()
    };
    let signature_links = SignatureLinks {
        resolved_signature: ResolvedSignatureState::Resolved(signature),
        ..SignatureLinks::default()
    };
    if plan.is_library_constructor()
        && store.symbol_node_links(plan.constructor) == Some(&symbol_links)
        && store.type_node_links(plan.constructor) == Some(&constructor_links)
        && store.signature_links(plan.node) == Some(&signature_links)
        && store.type_node_links(plan.node) == Some(&expression_links)
    {
        return Ok(selected);
    }
    assert!(store.set_symbol_node_links(plan.constructor, symbol_links));
    assert!(store.set_type_node_links(plan.constructor, constructor_links));
    assert!(store.set_signature_links(plan.node, signature_links));
    assert!(store.set_type_node_links(plan.node, expression_links));
    for (argument, &argument_type) in plan.arguments().zip(argument_types) {
        assert!(store.set_type_node_links(
            argument.node,
            TypeNodeLinks {
                resolved_type: Some(argument_type),
                ..TypeNodeLinks::default()
            },
        ));
    }
    for argument in &plan.type_arguments {
        assert!(store.set_type_node_links(
            argument.node,
            TypeNodeLinks {
                resolved_type: Some(argument.type_),
                ..TypeNodeLinks::default()
            },
        ));
    }
    Ok(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    })
}

// The source executor must complete the retained class before this use can publish.
fn resolved_source_class_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &SourceClassPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()));
    preflight_exported_constructor_binding(store, host, plan)?;
    let checked_arguments = class.has_checked_constructor_arguments();
    if class.symbol() != plan.provider_symbol()
        || !(class.has_own_default_constructor() || checked_arguments)
        || checked_arguments != plan.expression_arguments.is_some()
        || plan.argument.is_some()
        || !plan.additional_arguments.is_empty()
        || !plan.type_arguments.is_empty()
        || plan.parameter.is_some()
        || plan.executor.is_some()
        || plan.early_preparation
        || !source_class_plan_is_current(store, host, class)?
    {
        return Err(invalid());
    }
    if checked_arguments {
        preflight_source_class_expression_arguments(host, plan)?;
    }
    let declaration = host.node(class.declaration()).ok_or_else(invalid)?;
    let expression = host.node(plan.node).ok_or_else(invalid)?;
    if !class.declaration().is_for(plan.node.arena, plan.node.file)
        || declaration.range.end > expression.range.start
    {
        return Err(invalid());
    }
    let Some(members) = completed_source_class_members(store, host, class.symbol())? else {
        return Ok(None);
    };
    let selected = CheckedSourceDefaultNew {
        value_type: members.shells().value_type(),
        instance_type: members.shells().instance_type(),
        signature: members.default_construct_signature(),
    };
    // Completed source members also prove module-owned exported classes.
    // The legacy constructor reader remains restricted to unexported owners.
    if class.has_public_inherited_constructor() {
        let candidates = super::classes::source_class_expression_constructor_candidates(
            store,
            host,
            class.symbol(),
        )?
        .ok_or_else(invalid)?;
        if candidates
            .first()
            .is_none_or(|callable| callable.signature != selected.signature)
            || candidates.iter().any(|callable| {
                callable.owner != selected.value_type
                    || callable.return_type != Some(selected.instance_type)
            })
        {
            return Err(invalid());
        }
    } else if plan.resolved_symbol == class.symbol()
        && authenticated_class_constructor_value(store, class.symbol())
            != Some((selected.value_type, selected.signature))
    {
        return Err(invalid());
    }
    Ok(Some(selected))
}

fn preflight_generic_source_class_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    generic: &SourceGenericClassNewPlan,
) -> Result<(), SourceNewError> {
    let class = &generic.class;
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()));
    if !class.has_generic_constructor()
        || class.type_query_context().is_none()
        || plan.early_preparation
        || plan.argument.is_some()
        || !plan.additional_arguments.is_empty()
        || !plan.type_arguments.is_empty()
        || plan.parameter.is_some()
        || plan.executor.is_some()
        || constructor_value_symbol(store, plan.constructor, plan.resolved_symbol)?
            != class.symbol()
        || !source_class_plan_is_current(store, host, class)?
    {
        return Err(invalid());
    }
    let declaration = host.node(class.declaration()).ok_or_else(invalid)?;
    let expression = host.node(plan.node).ok_or_else(invalid)?;
    if !class.declaration().is_for(plan.node.arena, plan.node.file)
        || declaration.range.end > expression.range.start
        || generic_source_class_type_argument_nodes(host, plan.node, plan.constructor)?
            != generic.type_argument_nodes
    {
        return Err(invalid());
    }
    preflight_source_class_expression_arguments(host, plan)
}

fn generic_new_access_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    token: Option<&ClassBodyAccessToken>,
) -> Result<Option<(u32, TypeId)>, SourceNewError> {
    let SourceNewTarget::GenericSourceClass(generic) = &plan.target else {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    };
    let access = super::classes::source_class_constructor_access(
        store,
        host,
        plan.node,
        generic.class.symbol(),
        token,
    )?;
    if !access.allowed() {
        let code = match access.visibility() {
            ClassConstructorVisibility::Private => 2673,
            ClassConstructorVisibility::Protected => 2674,
            ClassConstructorVisibility::Public => {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                    generic.class.declaration(),
                )));
            }
        };
        return Ok(Some((code, access.declaring_type())));
    }
    Ok(generic
        .class
        .is_abstract()
        .then_some((2511, access.declaring_type())))
}

/// Go's `resolveErrorCall` returns this existing bootstrap signature and error type.
fn generic_new_error_signature(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(SignatureId, TypeId), SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(node));
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let signature = bootstrap.unknown_signature;
    let error_type =
        generic_new_error_signature_return_type(store, signature)?.ok_or_else(invalid)?;
    Ok((signature, error_type))
}

/// Reads the existing error-call sentinel without accepting another no-declaration signature.
pub(super) fn generic_new_error_signature_return_type(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
) -> Result<Option<TypeId>, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidConstructSignature(signature));
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Ok(None);
    };
    if signature != bootstrap.unknown_signature {
        return Ok(None);
    }
    let error_type = bootstrap.error_type;
    let record = store.signature(signature).ok_or_else(invalid)?;
    if record.flags() != SignatureFlags::NONE
        || record.declaration().is_some()
        || !record.type_parameters().is_empty()
        || !record.parameters().is_empty()
        || record.this_parameter().is_some()
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != Some(error_type)
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store
            .callable_signature_parameter_types(signature)
            .is_some()
        || store
            .function_signature_return_annotation(signature)
            .is_some()
        || store.validate_union_constituent(error_type).is_err()
    {
        return Err(invalid());
    }
    Ok(Some(error_type))
}

fn preflight_generic_new_signature(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    value_type: TypeId,
    signature: SignatureId,
    targets: Option<CanonicalArrayTargets>,
    access_diagnostic: Option<(u32, TypeId)>,
) -> Result<(), SourceNewError> {
    if access_diagnostic.is_some() {
        if generic_new_error_signature(store, plan.node)?.0 != signature {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                plan.node,
            )));
        }
    } else {
        preflight_generic_class_constructor_signature(store, value_type, signature, targets)
            .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
    }
    Ok(())
}

/// Checks the real caller authority and saved New signature before any demand.
pub(super) fn preflight_source_generic_class_new_with_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    access: Option<&ClassBodyAccessToken>,
) -> Result<(), SourceNewError> {
    if plan.is_generic_library_constructor() {
        preflight_direct_default_new_with_source_context(store, host, globals, options, plan)
            .map_err(|error| {
                trace_constructor_failure(
                    "required_preflight_error",
                    plan.node,
                    plan.constructor,
                    format_args!("error={error:?}"),
                );
                error
            })?;
        let candidates = resolve_library_new_candidates(store, host, globals, options, plan)
            .map_err(|error| {
                trace_constructor_failure(
                    "required_read_error",
                    plan.node,
                    plan.constructor,
                    format_args!("error={error:?}"),
                );
                error
            })?
            .ok_or_else(|| {
                let error = unsupported(SourceNewUnsupported::Constructor(plan.constructor));
                trace_constructor_failure(
                    "required_candidates_missing",
                    plan.node,
                    plan.constructor,
                    format_args!("candidate_state=missing error={error:?}"),
                );
                error
            })?;
        if let Some(signature) = exact_signature_cache(store, plan.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?
        {
            preflight_generic_class_constructor_signature(
                store,
                candidates.value_type,
                signature,
                Some(CanonicalArrayTargets::from_global_types(globals)),
            )
            .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
        }
        return Ok(());
    }
    preflight_direct_default_new(store, host, plan)?;
    let SourceNewTarget::GenericSourceClass(generic) = &plan.target else {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    };
    let invalid = || {
        invariant(SourceNewInvariant::InvalidClassPlan(
            generic.class.declaration(),
        ))
    };
    if generic.class.type_query_context() != Some(&ClassTypeQueryContext::new(globals, options)) {
        return Err(invalid());
    }
    let existing = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let targets = Some(CanonicalArrayTargets::from_global_types(globals));
    let constructors = super::classes::completed_source_class_constructors_with_context(
        store,
        host,
        generic.class.symbol(),
        targets,
        options.into(),
    )?
    .ok_or_else(|| unsupported(SourceNewUnsupported::Constructor(plan.constructor)))?;
    let access_diagnostic = generic_new_access_diagnostic(store, host, plan, access)?;
    if let Some(signature) = existing {
        preflight_generic_new_signature(
            store,
            plan,
            constructors.members().shells().value_type(),
            signature,
            targets,
            access_diagnostic,
        )?;
    }
    Ok(())
}

fn preflight_generic_new_arguments(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
) -> Result<(), SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let arguments = plan.checked_expression_arguments().ok_or_else(invalid)?;
    if arguments.len() != argument_types.len()
        || plan
            .written_type_argument_nodes()
            .filter(|nodes| !nodes.is_empty())
            .map(<[NodeRef]>::len)
            != explicit_type_arguments
                .filter(|types| !types.is_empty())
                .map(<[TypeId]>::len)
    {
        return Err(invalid());
    }
    for (argument, &type_) in arguments.iter().zip(argument_types) {
        if exact_type_cache(store, argument.node).map_err(|()| invalid())? != Some(type_) {
            return Err(invalid());
        }
    }
    if let (Some(nodes), Some(types)) =
        (plan.written_type_argument_nodes(), explicit_type_arguments)
    {
        for (&node, &type_) in nodes.iter().zip(types) {
            if store.type_payload(type_).is_none()
                || exact_type_cache(store, node)
                    .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(node)))?
                    .is_some_and(|cached| cached != type_)
            {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(node)));
            }
        }
    }
    Ok(())
}

fn generic_constructor_error(node: NodeRef, error: GenericMethodCallError) -> SourceNewError {
    let mut record = [0u8; 1024];
    let length = {
        let mut buffer = &mut record[..1023];
        let _ = std::io::Write::write_fmt(
            &mut buffer,
            format_args!(
                "ts-rust-generic-constructor-error expression={node:?} raw_error={error:?}"
            ),
        );
        1023 - buffer.len()
    };
    let length = std::str::from_utf8(&record[..length])
        .map_or_else(|error| error.valid_up_to(), |_| length);
    record[length] = b'\n';
    let _ = std::io::Write::write_all(&mut std::io::stderr().lock(), &record[..=length]);
    match error {
        GenericMethodCallError::Generic(GenericCallVectorError::Conditional(error)) => {
            match error {
                ConditionalTypeError::Relation(error) => SourceNewError::Call {
                    node,
                    error: super::calls::DirectCallError::Relation(error),
                },
                ConditionalTypeError::Declared(error) => error.into(),
                ConditionalTypeError::Instantiation(error) => generic_constructor_error(
                    node,
                    GenericMethodCallError::Generic(GenericCallVectorError::Instantiation(error)),
                ),
                ConditionalTypeError::MissingBootstrap => SourceNewError::Call {
                    node,
                    error: super::calls::DirectCallError::Relation(
                        super::RelationUnavailable::MissingBootstrap,
                    ),
                },
                ConditionalTypeError::Capacity => invariant(SourceNewInvariant::Capacity(node)),
                ConditionalTypeError::InvalidNode(node)
                | ConditionalTypeError::InvalidTypeNodeCache(node) => {
                    invariant(SourceNewInvariant::InvalidExpressionCache(node))
                }
                ConditionalTypeError::InvalidSignature(signature) => SourceNewError::Call {
                    node,
                    error: super::calls::DirectCallError::Invariant(
                        super::calls::DirectCallInvariant::InvalidSignature(signature),
                    ),
                },
                ConditionalTypeError::InvalidType(_)
                | ConditionalTypeError::InvalidTypeParameter(_)
                | ConditionalTypeError::DuplicateTypeParameter(_)
                | ConditionalTypeError::InvalidAlias(_)
                | ConditionalTypeError::InvalidAliasSymbol(_)
                | ConditionalTypeError::InvalidRoot(_)
                | ConditionalTypeError::InvalidConditional(_)
                | ConditionalTypeError::InvalidMapper(_)
                | ConditionalTypeError::InvalidInstantiationArity { .. }
                | ConditionalTypeError::InvalidInstantiationCache(_)
                | ConditionalTypeError::InvalidConditionalResolution(_) => {
                    invariant(SourceNewInvariant::InvalidExpressionCache(node))
                }
                ConditionalTypeError::UnsupportedInference { .. }
                | ConditionalTypeError::TailRecursionLimit { .. }
                | ConditionalTypeError::Constraint(_)
                | ConditionalTypeError::Template(_)
                | ConditionalTypeError::Tuple(_)
                | ConditionalTypeError::Union(_) => {
                    unsupported(SourceNewUnsupported::Arguments(node))
                }
            }
        }
        GenericMethodCallError::Relation(error)
        | GenericMethodCallError::Direct(super::calls::DirectCallError::Relation(error))
        | GenericMethodCallError::Generic(GenericCallVectorError::Relation(error))
        | GenericMethodCallError::Generic(GenericCallVectorError::Inference(
            super::inference::NakedTypeCandidateError::Relation(error),
        )) => SourceNewError::Call {
            node,
            error: super::calls::DirectCallError::Relation(error),
        },
        GenericMethodCallError::Invalid(_)
        | GenericMethodCallError::Direct(super::calls::DirectCallError::Invariant(_))
        | GenericMethodCallError::Generic(GenericCallVectorError::Invariant(_)) => {
            invariant(SourceNewInvariant::InvalidExpressionCache(node))
        }
        GenericMethodCallError::Unsupported(_)
        | GenericMethodCallError::Direct(super::calls::DirectCallError::Unsupported(_))
        | GenericMethodCallError::Generic(
            GenericCallVectorError::Unsupported(_)
            | GenericCallVectorError::Inference(_)
            | GenericCallVectorError::Instantiation(_),
        ) => unsupported(SourceNewUnsupported::Arguments(node)),
    }
}

/// One checked request retained until every source diagnostic is prepared.
pub(super) struct PreparedSourceGenericNew {
    checked: CheckedSourceDefaultNew,
    resolution: Option<GenericMethodCallResolution>,
    access_diagnostic: Option<(u32, TypeId)>,
    existing_signature: Option<SignatureId>,
    argument_types: Vec<TypeId>,
    explicit_type_arguments: Option<Vec<TypeId>>,
}

impl PreparedSourceGenericNew {
    pub(super) fn resolution(&self) -> Option<&GenericMethodCallResolution> {
        self.resolution.as_ref()
    }

    pub(super) const fn access_diagnostic(&self) -> Option<(u32, TypeId)> {
        self.access_diagnostic
    }
}

fn validate_generic_new_instance(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    origin: TypeId,
    checked: CheckedSourceDefaultNew,
    resolution: &GenericMethodCallResolution,
    targets: Option<CanonicalArrayTargets>,
) -> Result<(), SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let GenericMethodCallSelection::Generic(selected) = &resolution.selected else {
        return Err(invalid());
    };
    if selected.projection().callee != checked.value_type
        || selected.projection().instantiation.signature != checked.signature
        || preflight_generic_class_constructor_signature(
            store,
            checked.value_type,
            checked.signature,
            targets,
        )
        .map_err(|error| generic_constructor_error(plan.node, error.into()))?
            != selected.projection().generic_signature
        || store
            .signature(checked.signature)
            .and_then(Signature::resolved_return_type)
            != Some(checked.instance_type)
    {
        return Err(invalid());
    }
    let reference =
        validate_direct_generic_reference(store, checked.instance_type).map_err(|_| invalid())?;
    if reference.target != origin
        || reference.type_arguments != selected.projection().instantiation.type_arguments
    {
        return Err(invalid());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_source_generic_class_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    plan: &SourceDefaultNewPlan,
    access: Option<&ClassBodyAccessToken>,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
) -> Result<PreparedSourceGenericNew, SourceNewError> {
    if plan.is_generic_library_constructor() {
        return check_source_generic_library_new(
            store,
            host,
            globals,
            options,
            session,
            plan,
            argument_types,
            explicit_type_arguments,
        );
    }
    preflight_source_generic_class_new_with_context(store, host, globals, options, plan, access)?;
    preflight_prepared_default_new_cache(store, host, plan)?;
    preflight_generic_new_arguments(store, plan, argument_types, explicit_type_arguments)?;
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let existing_signature = exact_signature_cache(store, plan.node).map_err(|()| invalid())?;
    let constructors = super::classes::completed_source_class_constructors_with_context(
        store,
        host,
        plan.provider_symbol(),
        Some(CanonicalArrayTargets::from_global_types(globals)),
        options.into(),
    )?
    .ok_or_else(invalid)?;
    let value_type = constructors.members().shells().value_type();
    let origin = constructors.members().shells().instance_type();
    if let Some(access_diagnostic) = generic_new_access_diagnostic(store, host, plan, access)? {
        let (signature, instance_type) = generic_new_error_signature(store, plan.node)?;
        if existing_signature.is_some_and(|existing| existing != signature) {
            return Err(invalid());
        }
        return Ok(PreparedSourceGenericNew {
            checked: CheckedSourceDefaultNew {
                value_type,
                instance_type,
                signature,
            },
            resolution: None,
            access_diagnostic: Some(access_diagnostic),
            existing_signature,
            argument_types: argument_types.to_vec(),
            explicit_type_arguments: explicit_type_arguments.map(<[TypeId]>::to_vec),
        });
    }
    let resolution = resolve_generic_class_constructor(
        store,
        globals,
        options.strict_function_types,
        GenericCallVectorRequest {
            form: super::calls::DirectCallForm::New,
            optional_chain: false,
            explicit_type_arguments,
            has_spread_argument: false,
            callee: value_type,
            arguments: argument_types,
        },
        existing_signature,
        session,
    )
    .map_err(|error| generic_constructor_error(plan.node, error))?
    .ok_or_else(|| unsupported(SourceNewUnsupported::Arguments(plan.node)))?;
    let GenericMethodCallSelection::Generic(selected) = &resolution.selected else {
        return Err(invalid());
    };
    let materialized = materialize_generic_call_vector_source(store, selected, existing_signature)
        .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
    let limit_mark = session.limit_event_mark();
    let instance_type = demand_generic_call_vector_return_with_session(store, selected, session)
        .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
    if session.limit_event_occurred_since(limit_mark) {
        return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
    }
    let checked = CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature: materialized.call_signature,
    };
    validate_generic_new_instance(
        store,
        plan,
        origin,
        checked,
        &resolution,
        Some(CanonicalArrayTargets::from_global_types(globals)),
    )?;
    Ok(PreparedSourceGenericNew {
        checked,
        resolution: Some(resolution),
        access_diagnostic: None,
        existing_signature,
        argument_types: argument_types.to_vec(),
        explicit_type_arguments: explicit_type_arguments.map(<[TypeId]>::to_vec),
    })
}

/// Publishes the exact prepared request only after diagnostic preparation succeeds.
#[allow(clippy::too_many_arguments)]
pub(super) fn publish_source_generic_class_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    _session: &mut InstantiationSession,
    plan: &SourceDefaultNewPlan,
    access: Option<&ClassBodyAccessToken>,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
    prepared: PreparedSourceGenericNew,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    if plan.is_generic_library_constructor() {
        return publish_source_generic_library_new(
            store,
            host,
            globals,
            options,
            plan,
            argument_types,
            explicit_type_arguments,
            prepared,
        );
    }
    preflight_source_generic_class_new_with_context(store, host, globals, options, plan, access)?;
    preflight_generic_new_arguments(store, plan, argument_types, explicit_type_arguments)?;
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    if prepared.argument_types != argument_types
        || prepared.explicit_type_arguments.as_deref() != explicit_type_arguments
        || exact_signature_cache(store, plan.node).map_err(|()| invalid())?
            != prepared.existing_signature
        || generic_new_access_diagnostic(store, host, plan, access)? != prepared.access_diagnostic
    {
        return Err(invalid());
    }
    let constructors = super::classes::completed_source_class_constructors_with_context(
        store,
        host,
        plan.provider_symbol(),
        Some(CanonicalArrayTargets::from_global_types(globals)),
        options.into(),
    )?
    .ok_or_else(invalid)?;
    if constructors.members().shells().value_type() != prepared.checked.value_type {
        return Err(invalid());
    }
    if let Some(resolution) = &prepared.resolution {
        if prepared.access_diagnostic.is_some() {
            return Err(invalid());
        }
        validate_generic_new_instance(
            store,
            plan,
            constructors.members().shells().instance_type(),
            prepared.checked,
            resolution,
            Some(CanonicalArrayTargets::from_global_types(globals)),
        )?;
        let GenericMethodCallSelection::Generic(selected) = &resolution.selected else {
            return Err(invalid());
        };
        if materialize_generic_call_vector_source(store, selected, prepared.existing_signature)
            .map_err(|error| generic_constructor_error(plan.node, error.into()))?
            .call_signature
            != prepared.checked.signature
        {
            return Err(invalid());
        }
    } else if prepared.access_diagnostic.is_none()
        || generic_new_error_signature(store, plan.node)?
            != (prepared.checked.signature, prepared.checked.instance_type)
    {
        return Err(invalid());
    }
    let checked = publish_default_new_links(store, host, plan, prepared.checked, argument_types)?;
    if let (Some(nodes), Some(types)) =
        (plan.written_type_argument_nodes(), explicit_type_arguments)
    {
        for (&node, &type_) in nodes.iter().zip(types) {
            assert!(store.set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                },
            ));
        }
    }
    Ok(checked)
}

#[allow(clippy::too_many_arguments)]
fn check_source_generic_library_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    plan: &SourceDefaultNewPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
) -> Result<PreparedSourceGenericNew, SourceNewError> {
    check_source_generic_library_new_with_context(
        store,
        host,
        globals,
        options,
        session,
        plan,
        argument_types,
        explicit_type_arguments,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_source_generic_constructor_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    plan: &SourceDefaultNewPlan,
    prefix: &[TypeId],
    methods: &[GenericConstructorContextMethod],
) -> Result<PreparedGenericConstructorContext, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    if !plan.is_generic_library_constructor()
        || plan
            .written_type_argument_nodes()
            .is_some_and(|arguments| !arguments.is_empty())
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
    }
    preflight_source_generic_class_new_with_context(store, host, globals, options, plan, None)?;
    preflight_prepared_default_new_cache_with_context(store, host, plan, Some((globals, options)))?;
    let arguments = plan.checked_expression_arguments().ok_or_else(invalid)?;
    if arguments.len() != prefix.len() + 1
        || arguments
            .iter()
            .zip(prefix)
            .any(|(argument, &type_)| exact_type_cache(store, argument.node) != Ok(Some(type_)))
    {
        return Err(invalid());
    }
    let candidates =
        resolve_library_new_candidates(store, host, globals, options, plan)?.ok_or_else(invalid)?;
    let existing_signature = exact_signature_cache(store, plan.node).map_err(|()| invalid())?;
    prepare_generic_constructor_context(
        store,
        globals,
        options.strict_function_types,
        GenericCallVectorRequest {
            form: super::calls::DirectCallForm::New,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee: candidates.value_type,
            arguments: prefix,
        },
        existing_signature,
        methods,
        session,
    )
    .map_err(|error| generic_constructor_error(plan.node, error))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_source_generic_library_new_with_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    plan: &SourceDefaultNewPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
    context: Option<&PreparedGenericConstructorContext>,
) -> Result<PreparedSourceGenericNew, SourceNewError> {
    preflight_source_generic_class_new_with_context(store, host, globals, options, plan, None)?;
    preflight_prepared_default_new_cache_with_context(store, host, plan, Some((globals, options)))?;
    preflight_generic_new_arguments(store, plan, argument_types, explicit_type_arguments)?;
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let candidates =
        resolve_library_new_candidates(store, host, globals, options, plan)?.ok_or_else(invalid)?;
    let existing_signature = exact_signature_cache(store, plan.node).map_err(|()| invalid())?;
    let limit_mark = session.limit_event_mark();
    let resolution = resolve_generic_class_constructor_with_context(
        store,
        globals,
        options.strict_function_types,
        GenericCallVectorRequest {
            form: super::calls::DirectCallForm::New,
            optional_chain: false,
            explicit_type_arguments,
            has_spread_argument: false,
            callee: candidates.value_type,
            arguments: argument_types,
        },
        existing_signature,
        session,
        context,
    )
    .map_err(|error| generic_constructor_error(plan.node, error))?
    .ok_or_else(|| unsupported(SourceNewUnsupported::Arguments(plan.node)))?;
    let (signature, instance_type) = match &resolution.selected {
        GenericMethodCallSelection::Generic(selected) => {
            let materialized =
                materialize_generic_call_vector_source(store, selected, existing_signature)
                    .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
            let result = demand_generic_call_vector_return_with_session(store, selected, session)
                .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
            (materialized.call_signature, result)
        }
        GenericMethodCallSelection::Fixed {
            signature,
            return_type,
        } => (*signature, *return_type),
    };
    if session.limit_event_occurred_since(limit_mark) {
        return Err(unsupported(SourceNewUnsupported::Arguments(plan.node)));
    }
    preflight_generic_class_constructor_signature(
        store,
        candidates.value_type,
        signature,
        Some(CanonicalArrayTargets::from_global_types(globals)),
    )
    .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
    Ok(PreparedSourceGenericNew {
        checked: CheckedSourceDefaultNew {
            value_type: candidates.value_type,
            instance_type,
            signature,
        },
        resolution: Some(resolution),
        access_diagnostic: None,
        existing_signature,
        argument_types: argument_types.to_vec(),
        explicit_type_arguments: explicit_type_arguments.map(<[TypeId]>::to_vec),
    })
}

#[allow(clippy::too_many_arguments)]
fn publish_source_generic_library_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
    prepared: PreparedSourceGenericNew,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    preflight_source_generic_class_new_with_context(store, host, globals, options, plan, None)?;
    preflight_generic_new_arguments(store, plan, argument_types, explicit_type_arguments)?;
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let candidates =
        resolve_library_new_candidates(store, host, globals, options, plan)?.ok_or_else(invalid)?;
    if prepared.argument_types != argument_types
        || prepared.explicit_type_arguments.as_deref() != explicit_type_arguments
        || prepared.existing_signature
            != exact_signature_cache(store, plan.node).map_err(|()| invalid())?
        || prepared.access_diagnostic.is_some()
        || prepared.checked.value_type != candidates.value_type
    {
        return Err(invalid());
    }
    let resolution = prepared.resolution.as_ref().ok_or_else(invalid)?;
    let signature = match &resolution.selected {
        GenericMethodCallSelection::Generic(selected) => {
            materialize_generic_call_vector_source(store, selected, prepared.existing_signature)
                .map_err(|error| generic_constructor_error(plan.node, error.into()))?
                .call_signature
        }
        GenericMethodCallSelection::Fixed {
            signature,
            return_type,
        } => {
            if *return_type != prepared.checked.instance_type {
                return Err(invalid());
            }
            *signature
        }
    };
    if signature != prepared.checked.signature
        || store
            .signature(signature)
            .and_then(Signature::resolved_return_type)
            != Some(prepared.checked.instance_type)
    {
        return Err(invalid());
    }
    preflight_generic_class_constructor_signature(
        store,
        candidates.value_type,
        signature,
        Some(CanonicalArrayTargets::from_global_types(globals)),
    )
    .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
    publish_default_new_links_with_context(
        store,
        host,
        plan,
        prepared.checked,
        argument_types,
        Some((globals, options)),
    )
}

fn preflight_direct_class_expression_arguments(
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
) -> Result<(), SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    if class.direct_plan().is_none()
        || class.is_abstract()
        || class.constructor_visibility() != ClassConstructorVisibility::Public
        || plan.early_preparation
        || plan.parameter.is_none()
        || plan.argument.is_some()
        || !plan.additional_arguments.is_empty()
        || !plan.type_arguments.is_empty()
        || plan.executor.is_some()
    {
        return Err(invalid());
    }
    let Some(arguments) = &plan.expression_arguments else {
        return Err(invalid());
    };
    let [argument] = arguments.nodes.as_slice() else {
        return Err(invalid());
    };
    let record = host.node(*argument).ok_or_else(invalid)?;
    let literal = match &record.data {
        NodeData::StringLiteral(value) => {
            record.kind == SyntaxKind::StringLiteral && value.token_flags.0 == 0
        }
        NodeData::NumericLiteral(value) => {
            record.kind == SyntaxKind::NumericLiteral && value.token_flags.0 == 0
        }
        NodeData::KeywordExpression(value) => {
            matches!(
                record.kind,
                SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword
            ) && value.flow_node.is_none()
        }
        _ => false,
    };
    if !literal {
        return Err(invalid());
    }
    preflight_source_class_expression_arguments(host, plan)
}

fn preflight_source_class_expression_arguments(
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
    let Some(arguments) = &plan.expression_arguments else {
        return Err(invalid());
    };
    let record = host.node(plan.node).ok_or_else(invalid)?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Err(invalid());
    };
    let actual = expression
        .arguments
        .as_ref()
        .map_or(&[][..], |arguments| arguments.nodes.as_slice());
    if record.kind != SyntaxKind::NewExpression
        || record.flags.0 != 0
        || expression.facts != 0
        || expression.expression != plan.constructor.node
        || expression.type_arguments.is_some()
            && !(plan.is_generic_source_class() || plan.is_generic_library_constructor())
        || actual.len() != arguments.nodes.len()
        || actual
            .iter()
            .zip(&arguments.nodes)
            .any(|(&node, reference)| {
                *reference != NodeRef::new(plan.node.arena, plan.node.file, node)
            })
        || arguments.expressions.as_ref().is_some_and(|expressions| {
            expressions.len() != arguments.nodes.len()
                || expressions
                    .iter()
                    .zip(&arguments.nodes)
                    .any(|(expression, node)| expression.node != *node)
        })
    {
        return Err(invalid());
    }
    let mut previous_end = host.node(plan.constructor).ok_or_else(invalid)?.range.end;
    for &argument in &arguments.nodes {
        let child = host.node(argument).ok_or_else(invalid)?;
        if child.parent != Some(plan.node.node)
            || child.flags.0 != 0
            || child.range.start < previous_end
            || child.range.end > record.range.end
            || matches!(
                child.kind,
                SyntaxKind::SpreadElement | SyntaxKind::OmittedExpression
            )
            || host
                .bound_file(argument)
                .is_none_or(|bound| !bound.contains(argument))
        {
            return Err(invalid());
        }
        previous_end = child.range.end;
    }
    Ok(())
}

/// A transient view of the complete, source-proven library construct suffix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceLibraryConstructorCandidates {
    pub(super) value_type: TypeId,
    pub(super) callables: Vec<ValidatedSingleCallable>,
}

fn resolve_library_new_candidates(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
) -> Result<Option<SourceLibraryConstructorCandidates>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let library = match &plan.target {
        SourceNewTarget::Library(library) => library,
        SourceNewTarget::GenericLibrary(generic) => {
            if !generic.library.is_named_generic()
                || generic_source_class_type_argument_nodes(host, plan.node, plan.constructor)?
                    != generic.type_argument_nodes
            {
                return Err(invalid());
            }
            &generic.library
        }
        _ => return Err(invalid()),
    };
    if plan.argument.is_some()
        || !plan.additional_arguments.is_empty()
        || !plan.type_arguments.is_empty()
        || plan.parameter.is_some()
        || plan.executor.is_some()
        || library.value_symbol() != plan.resolved_symbol
        || constructor_value_symbol(store, plan.constructor, plan.resolved_symbol)?
            != plan.resolved_symbol
    {
        return Err(invalid());
    }
    preflight_source_class_expression_arguments(host, plan)?;
    let (arena, bound) = host.source(plan.constructor).ok_or_else(invalid)?;
    let record = host.node(plan.constructor).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(invalid());
    };
    let expression = host.node(plan.node).ok_or_else(invalid)?;
    let NodeData::NewExpression(new_expression) = &expression.data else {
        return Err(invalid());
    };
    if !plan.constructor.is_for(plan.node.arena, plan.node.file)
        || record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || record.parent != Some(plan.node.node)
        || record.range.start < expression.range.start
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || !bound.contains(plan.constructor)
        || !bound.contains(plan.node)
        || new_expression.arguments.as_ref().is_some_and(|arguments| {
            record.range.end > arguments.range.start
                || arguments.range.end != expression.range.end
                || arguments.range.end.get() < arguments.range.start.get().saturating_add(2)
                || arena.source_text().is_some_and(|source| {
                    let open = usize::try_from(arguments.range.start.get()).ok();
                    let close = usize::try_from(arguments.range.end.get().saturating_sub(1)).ok();
                    open.is_none_or(|open| source.as_bytes().get(open) != Some(&b'('))
                        || close.is_none_or(|close| source.as_bytes().get(close) != Some(&b')'))
                })
        })
        || new_expression.arguments.is_none() && record.range.end != expression.range.end
    {
        return Err(invalid());
    }
    let mut callback_host = host.name_resolver_host(store)?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| {
                invariant(SourceNewInvariant::NameResolution {
                    node: plan.constructor,
                    error,
                })
            })?;
    if resolver
        .resolve(
            Some(CanonicalResolutionLocation::Bound(plan.constructor)),
            &identifier.text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|error| {
            invariant(SourceNewInvariant::NameResolution {
                node: plan.constructor,
                error,
            })
        })?
        != Some(plan.resolved_symbol)
    {
        return Err(invalid());
    }
    let current = match library.kind() {
        GlobalConstructorValueKind::TypeLiteral => {
            plan_global_constructor_value(store, host, globals, options, plan.resolved_symbol)
        }
        GlobalConstructorValueKind::NamedNongeneric => {
            plan_global_named_constructor(store, host, globals, options, plan.resolved_symbol)
        }
        GlobalConstructorValueKind::NamedGeneric => {
            plan_global_generic_constructor_value(store, host, globals, options, plan.resolved_symbol)
        }
        GlobalConstructorValueKind::SourceNamedGeneric => plan_source_generic_constructor_value(
            store,
            host,
            globals,
            options,
            plan.resolved_symbol,
        ),
    }
    .map_err(|error| {
        trace_constructor_failure(
            "provider_revalidate",
            plan.node,
            plan.constructor,
            format_args!("provider={:?} raw_error={error:?}", plan.resolved_symbol),
        );
        global_error::provider_error(plan.constructor, plan.resolved_symbol, error)
    })?;
    if current.as_ref() != Some(library.as_ref()) {
        return Err(invalid());
    }
    let Some(ready) = resolve_global_constructor_candidates(store, host, globals, options, library)
        .map_err(|error| {
            trace_constructor_failure(
                "provider_read",
                plan.node,
                plan.constructor,
                format_args!("provider={:?} raw_error={error:?}", plan.resolved_symbol),
            );
            global_error::provider_error(plan.constructor, plan.resolved_symbol, error)
        })?
    else {
        return Ok(None);
    };
    let value = ready.value();
    let value_type = value.constructor_type();
    let projection =
        super::callable_sets::validate_stored_callable_set_projection(store, value_type, false)
            .ok_or_else(invalid)?;
    if value.value_symbol() != plan.resolved_symbol
        || projection.owner != value_type
        || ready.signatures().is_empty()
        || projection.construct_signatures.len() != ready.signatures().len()
        || library.construct_declarations().len() != ready.signatures().len()
    {
        return Err(invalid());
    }
    let mut callables = Vec::with_capacity(ready.signatures().len());
    for ((signature, &projected), declaration) in ready
        .signatures()
        .iter()
        .zip(projection.construct_signatures.iter())
        .zip(library.construct_declarations())
    {
        let record = store.signature(projected).ok_or_else(invalid)?;
        let mut parameters = store
            .callable_signature_parameter_types(projected)
            .ok_or_else(invalid)?
            .to_vec();
        if signature.value() != value
            || signature.signature() != projected
            || signature.declaration() != declaration
            || record.declaration() != Some(declaration)
            || !record.flags().contains(SignatureFlags::CONSTRUCT)
            || record.flags().contains(SignatureFlags::ABSTRACT)
            || !library.is_named_generic() && !record.type_parameters().is_empty()
            || record.target().is_some()
            || record.mapper().is_some()
            || record.resolved_return_type() != Some(signature.return_type())
            || parameters.len() != record.parameters().len()
        {
            return Err(invalid());
        }
        let rest_parameter = if record.has_rest_parameter() {
            Some(parameters.pop().ok_or_else(invalid)?)
        } else {
            None
        };
        let min_argument_count =
            usize::try_from(record.min_argument_count()).map_err(|_| invalid())?;
        if min_argument_count > parameters.len() {
            return Err(invalid());
        }
        callables.push(ValidatedSingleCallable {
            owner: value_type,
            signature: projected,
            parameters,
            rest_parameter,
            min_argument_count,
            return_type: Some(signature.return_type()),
            strict_variance_exempt: false,
        });
    }
    Ok(Some(SourceLibraryConstructorCandidates {
        value_type,
        callables,
    }))
}

/// Checks available producer facts. Flow-dependent types still need the executor.
fn preflight_library_argument_caches(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    let Some(arguments) = plan.checked_expression_arguments() else {
        return Ok(());
    };
    let mut pending = arguments.iter().collect::<Vec<_>>();
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        let node = expression.node;
        let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(node));
        if !seen.insert(node)
            || host.node(node).is_none()
            || host
                .bound_file(node)
                .is_none_or(|bound| !bound.contains(node))
        {
            return Err(invalid());
        }
        let cached = exact_type_cache(store, node).map_err(|()| invalid())?;
        let symbol = exact_symbol_cache(store, node).map_err(|()| invalid())?;
        match &expression.kind {
            PlannedExpressionKind::Call(_) => {
                super::source_calls::preflight_call_links(store, node).map_err(|_| invalid())?;
            }
            PlannedExpressionKind::SuperCall(_) => {
                super::source_calls::preflight_super_call_links(store, node)
                    .map_err(|_| invalid())?;
            }
            _ => {
                exact_signature_cache(store, node).map_err(|()| invalid())?;
            }
        }
        if let PlannedExpressionKind::Identifier(read) = &expression.kind
            && symbol.is_some_and(|symbol| symbol != read.resolved_symbol)
        {
            return Err(invalid());
        }
        if let PlannedExpressionKind::Object { plan: object, .. } = &expression.kind {
            let state = object_literal_state(store, object).map_err(|_| invalid())?;
            if cached.is_some_and(|cached| {
                state.is_none_or(|state| !state.is_resolved() || state.type_id() != cached)
            }) {
                return Err(invalid());
            }
        }
        if let PlannedExpressionKind::New(nested) = &expression.kind {
            preflight_direct_default_new_with_source_context(
                store, host, globals, options, nested,
            )?;
        }
        if let Some(cached) = cached {
            let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
            let regular = match &expression.kind {
                PlannedExpressionKind::String(value) => {
                    Some(bootstrap.cached_string_literal_type(value))
                }
                PlannedExpressionKind::Number { value, .. } => {
                    Some(bootstrap.cached_number_literal_type(*value))
                }
                PlannedExpressionKind::BigInt { value, .. } => {
                    Some(bootstrap.cached_bigint_literal_type(value))
                }
                PlannedExpressionKind::Boolean(value) => Some(Some(if *value {
                    bootstrap.regular_true_type
                } else {
                    bootstrap.regular_false_type
                })),
                _ => None,
            };
            if let Some(regular) = regular {
                let regular = regular.ok_or_else(invalid)?;
                store
                    .validate_union_constituent(regular)
                    .map_err(|_| invalid())?;
                let Some(TypeData::Literal(literal)) =
                    store.type_payload(regular).map(TypeRecord::data)
                else {
                    return Err(invalid());
                };
                if literal.regular_type != regular
                    || cached != regular && literal.fresh_type != Some(cached)
                {
                    return Err(invalid());
                }
                store
                    .validate_union_constituent(cached)
                    .map_err(|_| invalid())?;
            }
            let known = match &expression.kind {
                PlannedExpressionKind::Null => Some(bootstrap.null_widening_type),
                PlannedExpressionKind::GlobalUndefined => Some(bootstrap.undefined_widening_type),
                PlannedExpressionKind::RegularExpression(type_) => Some(*type_),
                PlannedExpressionKind::Parenthesized(_)
                    if expression.unparenthesized().node != node =>
                {
                    Some(
                        exact_type_cache(store, expression.unparenthesized().node)
                            .map_err(|()| invalid())?
                            .ok_or_else(invalid)?,
                    )
                }
                _ => None,
            };
            if known.is_some_and(|expected| expected != cached) {
                return Err(invalid());
            }
        }
        expression.new_argument_children(&mut pending);
    }
    Ok(())
}

/// Requires prepared use-site slots and validates every candidate before demand.
pub(super) fn source_library_constructor_candidates(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
) -> Result<SourceLibraryConstructorCandidates, SourceNewError> {
    preflight_direct_default_new_with_source_context(store, host, globals, options, plan)?;
    preflight_prepared_default_new_cache_with_context(store, host, plan, Some((globals, options)))?;
    if plan.checked_expression_arguments().is_none() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    resolve_library_new_candidates(store, host, globals, options, plan)?.ok_or_else(|| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })
}

pub(super) fn source_constructor_argument_contextual_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    argument_index: usize,
) -> Result<Option<TypeId>, SourceNewError> {
    if !plan.is_library_constructor() {
        return source_class_constructor_argument_contextual_type(
            store,
            host,
            globals,
            plan,
            argument_index,
        );
    }
    let candidates = source_library_constructor_candidates(store, host, globals, options, plan)?;
    let arguments = plan
        .checked_expression_arguments()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    if argument_index >= arguments.len() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    let single = candidates.callables.len() == 1;
    let candidates = candidates.callables.iter().filter(|candidate| {
        single
            || arguments.len() >= candidate.min_argument_count
                && (candidate.rest_parameter.is_some()
                    || arguments.len() <= candidate.parameters.len())
    });
    super::source_calls::common_fixed_argument_contextual_type(
        store,
        globals,
        candidates,
        argument_index,
    )
    .map_err(|error| SourceNewError::Call {
        node: plan.node,
        error,
    })
}

/// Publishes only a selected original candidate after source diagnostics succeed.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_source_library_expression_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    candidates: &SourceLibraryConstructorCandidates,
    checked_arguments: &[CheckedExpressionTypes],
    resolution: &super::calls::DirectCallResolution,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    let current = source_library_constructor_candidates(store, host, globals, options, plan)?;
    if &current != candidates
        || !current.callables.iter().any(|candidate| {
            candidate.signature == resolution.projection.signature
                && candidate.return_type == Some(resolution.projection.return_type)
        })
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    let selected = CheckedSourceDefaultNew {
        value_type: current.value_type,
        instance_type: resolution.projection.return_type,
        signature: resolution.projection.signature,
    };
    let argument_cache_types = checked_arguments
        .iter()
        .map(CheckedExpressionTypes::raw)
        .collect::<Vec<_>>();
    publish_default_new_links_with_context(
        store,
        host,
        plan,
        selected,
        &argument_cache_types,
        Some((globals, options)),
    )
}

pub(super) fn source_class_constructor_argument_contextual_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    plan: &SourceDefaultNewPlan,
    argument_index: usize,
) -> Result<Option<TypeId>, SourceNewError> {
    let SourceNewTarget::SourceClass(class) = &plan.target else {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    };
    let selected =
        resolved_source_class_constructor(store, host, plan, class)?.ok_or_else(|| {
            invariant(SourceNewInvariant::InvalidConstructorCache(
                plan.constructor,
            ))
        })?;
    let candidates = super::classes::source_class_expression_constructor_candidates(
        store,
        host,
        class.symbol(),
    )?
    .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(class.declaration())))?;
    if candidates
        .first()
        .is_none_or(|callable| callable.signature != selected.signature)
        || candidates
            .iter()
            .any(|callable| callable.owner != selected.value_type)
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            selected.signature,
        )));
    }
    let arity = plan
        .expression_arguments
        .as_ref()
        .map_or(0, |arguments| arguments.nodes.len());
    let mut contextual = None;
    for callable in &candidates {
        if class.has_public_inherited_constructor()
            && (arity < callable.min_argument_count || arity > callable.parameters.len())
        {
            continue;
        }
        let Some(candidate) =
            super::calls::try_get_type_at_position(store, Some(globals), callable, argument_index)
                .map_err(|error| SourceNewError::Call {
                    node: plan.node,
                    error,
                })?
        else {
            return Ok(None);
        };
        if contextual.is_some_and(|previous| previous != candidate) {
            return Ok(None);
        }
        contextual = Some(candidate);
    }
    Ok(contextual)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_source_class_expression_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    session: &mut super::instantiate::InstantiationSession,
    plan: &SourceDefaultNewPlan,
    argument_types: &[TypeId],
) -> Result<(CheckedSourceDefaultNew, super::calls::DirectCallResolution), SourceNewError> {
    preflight_direct_default_new(store, host, plan)?;
    if plan
        .checked_expression_arguments()
        .is_none_or(|arguments| arguments.len() != argument_types.len())
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    let (selected, candidates) = match &plan.target {
        SourceNewTarget::SourceClass(class) => {
            let selected =
                resolved_source_class_constructor(store, host, plan, class)?.ok_or_else(|| {
                    invariant(SourceNewInvariant::InvalidConstructorCache(
                        plan.constructor,
                    ))
                })?;
            let candidates = super::classes::source_class_expression_constructor_candidates(
                store,
                host,
                class.symbol(),
            )?
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassPlan(class.declaration())))?;
            (selected, candidates)
        }
        SourceNewTarget::Class(class) => {
            let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(class.declaration()));
            let members = execute_nongeneric_class_member_query(store, host, class)?;
            let selected = CheckedSourceDefaultNew {
                value_type: members.shells().value_type(),
                instance_type: members.shells().instance_type(),
                signature: members.default_construct_signature(),
            };
            validate_selected_default_signature(
                store,
                host,
                plan,
                class,
                selected.value_type,
                selected.instance_type,
                selected.signature,
            )?;
            let StoredCallableSetValidation::Valid {
                family,
                projection,
                ..
            } = validate_stored_callable_set(store, selected.value_type)
            else {
                return Err(invalid());
            };
            if family != CallableFamily::DeclaredCallSignatures
                || projection.owner != selected.value_type
                || !projection.call_signatures.is_empty()
                || projection.construct_signatures.as_ref()
                    != std::slice::from_ref(&selected.signature)
            {
                return Err(invalid());
            }
            let signature = store.signature(selected.signature).ok_or_else(invalid)?;
            let parameters = signature
                .parameters()
                .iter()
                .map(|&parameter| {
                    let links = store.value_symbol_links(parameter).ok_or_else(invalid)?;
                    let type_ = links.resolved_type.ok_or_else(invalid)?;
                    if links
                        != &(ValueSymbolLinks {
                            resolved_type: Some(type_),
                            ..ValueSymbolLinks::default()
                        })
                        || store.type_payload(type_).is_none()
                    {
                        return Err(invalid());
                    }
                    Ok(type_)
                })
                .collect::<Result<Vec<_>, SourceNewError>>()?;
            let callable = ValidatedSingleCallable {
                owner: selected.value_type,
                signature: selected.signature,
                parameters,
                rest_parameter: None,
                min_argument_count: usize::try_from(signature.min_argument_count())
                    .map_err(|_| invalid())?,
                return_type: signature.resolved_return_type(),
                strict_variance_exempt: true,
            };
            (selected, vec![callable])
        }
        _ => {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                plan.node,
            )));
        }
    };
    if candidates
        .first()
        .is_none_or(|callable| callable.signature != selected.signature)
        || candidates.iter().any(|callable| {
            callable.owner != selected.value_type
                || callable.return_type != Some(selected.instance_type)
        })
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            selected.signature,
        )));
    }
    let existing_signature = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let resolution = super::calls::resolve_direct_call_candidates_with_session(
        store,
        globals,
        strict_function_types,
        super::calls::DirectCallRequest {
            form: super::calls::DirectCallForm::New,
            optional_chain: false,
            type_argument_count: 0,
            has_spread_argument: false,
            callee: selected.value_type,
            arguments: argument_types,
        },
        &candidates,
        existing_signature,
        session,
    )
    .map_err(|error| SourceNewError::Call {
        node: plan.node,
        error,
    })?;
    if let Some(existing) = existing_signature
        && existing != resolution.projection.signature
    {
        return Err(SourceNewError::Call {
            node: plan.node,
            error: super::calls::DirectCallInvariant::InvalidSignature(existing).into(),
        });
    }
    if !candidates
        .iter()
        .any(|callable| callable.signature == resolution.projection.signature)
        || resolution.projection.return_type != selected.instance_type
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    let selected = CheckedSourceDefaultNew {
        signature: resolution.projection.signature,
        ..selected
    };
    let checked = publish_default_new_links(store, host, plan, selected, argument_types)?;
    Ok((checked, resolution))
}

fn preflight_prepared_default_new_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_prepared_default_new_cache_with_context(store, host, plan, None)
}

fn preflight_prepared_default_new_cache_with_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<(), SourceNewError> {
    if store.symbol_node_links(plan.constructor).is_none()
        || store.type_node_links(plan.constructor).is_none()
        || store.signature_links(plan.node).is_none()
        || store.type_node_links(plan.node).is_none()
        || plan
            .arguments()
            .any(|argument| store.type_node_links(argument.node).is_none())
        || plan
            .type_arguments
            .iter()
            .any(|argument| store.type_node_links(argument.node).is_none())
        || plan
            .written_type_argument_nodes()
            .unwrap_or_default()
            .iter()
            .any(|argument| store.type_node_links(*argument).is_none())
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    preflight_default_new_cache_with_context(store, host, plan, source_context)
}

fn resolved_declared_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    declared: &SourceDeclaredConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let Some(value_type) = exact_type_cache(store, declared.annotation).map_err(|()| invalid())?
    else {
        if exact_class_value_type(store, plan.resolved_symbol)?.is_some() {
            return Err(invalid());
        }
        return Ok(None);
    };
    if exact_class_value_type(store, plan.resolved_symbol)?
        .is_some_and(|cached| cached != value_type)
    {
        return Err(invalid());
    }

    let StoredCallableSetValidation::Valid {
        family: CallableFamily::DeclaredCallSignatures,
        projection,
        ..
    } = validate_stored_callable_set(store, value_type)
    else {
        return Err(invalid());
    };
    if projection.owner != value_type || projection.construct_signatures.is_empty() {
        return Err(invalid());
    }
    let Some(signature) = projection
        .construct_signatures
        .iter()
        .copied()
        .find(|signature| {
            store
                .signature(*signature)
                .is_some_and(|record| record.declaration() == Some(declared.declaration))
        })
    else {
        return Err(invalid());
    };
    let record = store.signature(signature).ok_or_else(invalid)?;
    let Some(instance_type) = record.resolved_return_type() else {
        return Err(invalid());
    };
    let allowed_flags = SignatureFlags::CONSTRUCT | SignatureFlags::HAS_LITERAL_TYPES;
    if !record.flags().contains(SignatureFlags::CONSTRUCT)
        || record.flags().intersects(SignatureFlags::ABSTRACT)
        || record.flags().bits() & !allowed_flags.bits() != 0
        || record.parameters()
            != declared
                .signature_parameter
                .map(|parameter| parameter.symbol)
                .as_slice()
        || usize::try_from(record.min_argument_count()).ok() != Some(declared.min_argument_count)
        || record.resolved_min_argument_count() != -1
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.composite().is_some()
        || store.callable_signature_parameter_types(signature)
            != Some(
                declared
                    .signature_parameter
                    .map(|parameter| parameter.type_)
                    .as_slice(),
            )
        || store.type_payload(instance_type).is_none()
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }

    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    }))
}

fn resolved_declared_class_union_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    union: &SourceClassUnionConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let Some(candidates) = class_union_constructor_candidates(store, plan, union)? else {
        return Ok(None);
    };
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let value_type = candidates.value_type;
    if union.classes.iter().any(ClassMemberQueryPlan::is_abstract) {
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        let signature = bootstrap.unknown_signature;
        let record = store.signature(signature).ok_or_else(invalid)?;
        if record.flags() != SignatureFlags::NONE
            || record.declaration().is_some()
            || !record.parameters().is_empty()
            || !record.type_parameters().is_empty()
            || record.min_argument_count() != 0
            || record.resolved_min_argument_count() != -1
            || record.this_parameter().is_some()
            || record.resolved_return_type() != Some(bootstrap.error_type)
            || record.resolved_type_predicate().is_some()
            || record.target().is_some()
            || record.mapper().is_some()
            || record.composite().is_some()
            || record.isolated_signature_type().is_some()
        {
            return Err(invalid());
        }
        return Ok(Some(CheckedSourceDefaultNew {
            value_type,
            instance_type: bootstrap.error_type,
            signature,
        }));
    }
    if let [signature] = candidates.signatures.as_slice() {
        return Ok(Some(CheckedSourceDefaultNew {
            value_type,
            instance_type: candidates.instance_types[0],
            signature: *signature,
        }));
    }
    let structured = store
        .type_payload(value_type)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    if structured == &StructuredTypeData::default() {
        return Ok(None);
    }
    let StoredCallableSetValidation::Valid {
        family: CallableFamily::DeclaredCallSignatures,
        projection,
        ..
    } = validate_stored_callable_set(store, value_type)
    else {
        return Err(invalid());
    };
    let [signature] = projection.construct_signatures.as_ref() else {
        return Err(invalid());
    };
    let instance_type = store
        .signature(*signature)
        .and_then(Signature::resolved_return_type)
        .ok_or_else(invalid)?;
    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature: *signature,
    }))
}

fn materialize_class_union_constructor(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    union: &SourceClassUnionConstructorPlan,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    if let Some(resolved) = resolved_declared_class_union_constructor(store, plan, union)? {
        return Ok(resolved);
    }
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let candidates = class_union_constructor_candidates(store, plan, union)?.ok_or_else(invalid)?;
    let Some(first) = candidates.signatures.first().copied() else {
        return Err(invalid());
    };
    if !store.try_reserve_signatures(1) {
        return Err(invariant(SourceNewInvariant::Capacity(plan.node)));
    }
    // Upstream removeSubtypes keeps unrelated class instances. These direct
    // class plans have no object base, so their return union needs no reduction.
    let mut prepared = store
        .prepare_type_query_types(&[], &[], &[], 1, 0)
        .map_err(|error| literal_cache_error(plan.node, error))?;
    let instance_type = store
        .literal_union_type_prepared(&candidates.instance_types, None, &mut prepared)
        .map_err(|error| literal_cache_error(plan.node, error))?;
    let composite = store
        .create_composite_signature(true, candidates.signatures)
        .ok_or_else(invalid)?;
    let signature = store.clone_signature(first).map_err(|_| invalid())?;
    assert!(store.set_signature_composite(signature, Some(composite)));
    assert!(store.set_signature_resolved_return_type(signature, Some(instance_type)));
    assert!(store.set_structured_type_members(
        candidates.value_type,
        None,
        None,
        None,
        Some(vec![signature]),
        None,
    ));
    resolved_declared_class_union_constructor(store, plan, union)?.ok_or_else(invalid)
}

fn class_union_constructor_candidates(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    union: &SourceClassUnionConstructorPlan,
) -> Result<Option<SourceClassUnionConstructorCandidates>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let value_type = match union.provider {
        SourceClassUnionConstructorProvider::Ambient(annotation) => {
            exact_type_cache(store, annotation).map_err(|()| invalid())?
        }
        SourceClassUnionConstructorProvider::ArrayCallback { receiver, .. } => {
            let Some(receiver_type) = exact_type_cache(store, receiver).map_err(|()| invalid())?
            else {
                if exact_class_value_type(store, plan.resolved_symbol)?.is_some() {
                    return Err(invalid());
                }
                return Ok(None);
            };
            let receiver_record = store.type_payload(receiver_type).ok_or_else(invalid)?;
            let TypeData::TypeReference(reference) = receiver_record.data() else {
                return Err(invalid());
            };
            let Some([element]) = reference.resolved_type_arguments.as_deref() else {
                return Err(invalid());
            };
            let target = reference.object.target.ok_or_else(invalid)?;
            let target_owner = store
                .type_payload(target)
                .and_then(TypeRecord::symbol)
                .ok_or_else(invalid)?;
            let global_array = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source("Array"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .ok_or_else(invalid)?;
            if receiver_record.flags() != TypeFlags::OBJECT
                || !receiver_record
                    .object_flags()
                    .contains(ObjectFlags::ARRAY_LITERAL)
                || receiver_record.symbol() != Some(global_array)
                || reference.object.mapper.is_some()
                || target_owner != global_array
            {
                return Err(invalid());
            }
            Some(*element)
        }
    };
    let Some(value_type) = value_type else {
        if exact_class_value_type(store, plan.resolved_symbol)?.is_some() {
            return Err(invalid());
        }
        return Ok(None);
    };
    if exact_class_value_type(store, plan.resolved_symbol)?
        .is_some_and(|cached| cached != value_type)
        || store.validate_union_constituent(value_type).is_err()
    {
        return Err(invalid());
    }
    let candidates = match store.type_payload(value_type).map(TypeRecord::data) {
        Some(TypeData::Union(candidates)) => candidates.union.types.as_slice(),
        Some(TypeData::Object(_))
            if matches!(
                union.provider,
                SourceClassUnionConstructorProvider::ArrayCallback { .. }
            ) =>
        {
            std::slice::from_ref(&value_type)
        }
        _ => return Err(invalid()),
    };
    if candidates.len() > union.classes.len()
        || candidates.len() != union.classes.len()
            && matches!(
                union.provider,
                SourceClassUnionConstructorProvider::Ambient(_)
            )
    {
        return Err(invalid());
    }

    let mut signatures = Vec::with_capacity(candidates.len());
    let mut instance_types = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let owner = store
            .type_payload(*candidate)
            .and_then(TypeRecord::symbol)
            .ok_or_else(invalid)?;
        let class = union
            .classes
            .iter()
            .find(|class| class.symbol() == owner)
            .ok_or_else(invalid)?;
        let (value, signature) =
            authenticated_class_constructor_value(store, owner).ok_or_else(invalid)?;
        let record = store.signature(signature).ok_or_else(invalid)?;
        let expected_flags = SignatureFlags::CONSTRUCT
            | if class.is_abstract() {
                SignatureFlags::ABSTRACT
            } else {
                SignatureFlags::NONE
            };
        let instance_type = record.resolved_return_type().ok_or_else(invalid)?;
        if value != *candidate
            || record.flags() != expected_flags
            || !record.parameters().is_empty()
            || !record.type_parameters().is_empty()
            || record.min_argument_count() != 0
            || record.resolved_min_argument_count() != -1
            || record.this_parameter().is_some()
            || record.target().is_some()
            || record.mapper().is_some()
            || record.composite().is_some()
            || store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                != Some(instance_type)
        {
            return Err(invalid());
        }
        signatures.push(signature);
        instance_types.push(instance_type);
    }
    if signatures.is_empty() {
        return Err(invalid());
    }
    Ok(Some(SourceClassUnionConstructorCandidates {
        value_type,
        signatures,
        instance_types,
    }))
}

fn resolved_global_object_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalObjectConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let Some(value_type) = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    if exact_type_cache(store, global.annotation)
        .map_err(|()| invalid())?
        .is_some_and(|cached| cached != value_type)
        || exact_symbol_cache(store, global.annotation)
            .map_err(|()| invalid())?
            .is_some_and(|symbol| symbol != global.owner)
        || exact_symbol_cache(store, global.return_annotation)
            .map_err(|()| invalid())?
            .is_some_and(|symbol| symbol != plan.resolved_symbol)
        || exact_class_value_type(store, plan.resolved_symbol)?
            .is_some_and(|cached| cached != value_type)
    {
        return Err(invalid());
    }
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value.data() else {
        return Err(invalid());
    };
    let signature =
        if let Some(signatures) = interface.reference.object.structured.signatures.as_deref() {
            let Some(signature) = signatures
                .iter()
                .skip(interface.reference.object.structured.call_signature_count)
                .copied()
                .find(|signature| {
                    store.signature(*signature).is_some_and(|signature| {
                        signature.declaration() == Some(global.declaration)
                    })
                })
            else {
                return Ok(None);
            };
            signature
        } else {
            if interface.reference.object.structured.call_signature_count != 0 {
                return Err(invalid());
            }
            let Some(signature) = store
                .signature_links(global.declaration)
                .and_then(|links| links.resolved_signature.signature())
            else {
                return Ok(None);
            };
            signature
        };
    validate_global_object_constructor_signature(
        store,
        plan.constructor,
        plan.resolved_symbol,
        global,
        value_type,
        signature,
    )
    .map(Some)
}

fn validate_global_object_constructor_signature(
    store: &CanonicalTypeMapperStore,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    global: &SourceGlobalObjectConstructorPlan,
    value_type: TypeId,
    signature: SignatureId,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidConstructorCache(constructor));
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let record = store.signature(signature).ok_or_else(invalid)?;
    let allowed_flags = SignatureFlags::CONSTRUCT | SignatureFlags::HAS_LITERAL_TYPES;
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || record.declaration() != Some(global.declaration)
        || !record.flags().contains(SignatureFlags::CONSTRUCT)
        || record.flags().bits() & !allowed_flags.bits() != 0
        || record.parameters() != [global.parameter.symbol]
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != Some(global.object_type)
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.signature_links(global.declaration)
            != Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        || store.value_symbol_links(global.parameter.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(global.parameter.type_),
                ..ValueSymbolLinks::default()
            })
        || store
            .callable_signature_parameter_types(signature)
            .is_some_and(|types| types != [global.parameter.type_])
        || store
            .function_signature_return_annotation(signature)
            .is_some_and(|annotation| annotation != (global.return_annotation, false))
        || exact_type_cache(store, global.return_annotation)
            .map_err(|()| invalid())?
            .is_some_and(|cached| cached != global.object_type)
        || store
            .declared_type_links(resolved_symbol)
            .and_then(|links| links.declared_type)
            != Some(global.object_type)
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }

    Ok(CheckedSourceDefaultNew {
        value_type,
        instance_type: global.object_type,
        signature,
    })
}

/// Validates a source-published global constructor before its interface is expanded.
pub(super) fn authenticated_lazy_global_object_constructor_return(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    signature: SignatureId,
) -> Option<TypeId> {
    let declaration = store.signature(signature)?.declaration()?;
    let SourceNodeParent::Parent(owner_declaration) = store.source_node_parent(declaration)? else {
        return None;
    };
    let bound = host.bound_file(owner_declaration)?;
    let facts = bound.source_facts()?;
    if !facts.is_default_library()
        || !facts.is_declaration_file()
        || facts.is_javascript_file()
        || facts.is_external_or_common_js_module()
    {
        return None;
    }
    let owner = bound
        .symbol(owner_declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))?;
    let owner_name = store.symbol(owner)?.name().as_utf8()?;
    let instance_name = match owner_name {
        "ObjectConstructor" => "Object",
        "BooleanConstructor" => "Boolean",
        _ => return None,
    };
    let globals = store.symbol_table(store.intrinsic_bootstrap()?.globals)?;
    if globals
        .get_source(owner_name)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        != Some(owner)
    {
        return None;
    }
    let instance = globals
        .get_source(instance_name)
        .and_then(|symbol| store.get_merged_symbol(symbol))?;
    let value_declaration = store.symbol(instance)?.value_declaration()?;
    let global = plan_global_object_constructor(store, host, value_declaration, instance).ok()?;
    let value_type = store.declared_type_links(owner)?.declared_type?;
    let value = store.type_payload(value_type)?;
    let TypeData::Interface(interface) = value.data() else {
        return None;
    };
    if global.owner != owner
        || global.declaration != declaration
        || value.object_flags() != ObjectFlags::INTERFACE
        || interface.declared_members_resolved
        || interface.declared_members.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || interface.reference.object.structured != StructuredTypeData::default()
        || store.type_has_declared_call_set_provenance(value_type)
        || store
            .declared_call_set_type_for_signature(signature)
            .is_some()
        || store
            .callable_signature_parameter_types(signature)
            .is_some()
        || exact_type_cache(store, global.annotation).ok()? != Some(value_type)
        || exact_symbol_cache(store, global.annotation).ok()? != Some(owner)
        || exact_class_value_type(store, instance).ok()? != Some(value_type)
        || exact_type_cache(store, global.return_annotation).ok()? != Some(global.object_type)
        || exact_symbol_cache(store, global.return_annotation).ok()? != Some(instance)
        || store.function_signature_return_annotation(signature)
            != Some((global.return_annotation, false))
    {
        return None;
    }
    validate_global_object_constructor_signature(
        store,
        value_declaration,
        instance,
        &global,
        value_type,
        signature,
    )
    .ok()
    .map(|checked| checked.instance_type)
}

fn resolved_global_date_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalDateConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let instance_type = store
        .declared_type_links(plan.resolved_symbol)
        .and_then(|links| links.declared_type);
    let value_type = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type);
    let annotation = exact_type_cache(store, global.annotation).map_err(|()| invalid())?;
    let annotation_symbol = exact_symbol_cache(store, global.annotation).map_err(|()| invalid())?;
    let date_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    let return_symbol =
        exact_symbol_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if annotation.is_some_and(|type_| Some(type_) != value_type)
        || annotation_symbol.is_some_and(|symbol| symbol != global.owner)
        || date_value.is_some_and(|type_| Some(type_) != value_type)
        || return_annotation.is_some_and(|type_| Some(type_) != instance_type)
        || return_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
    {
        return Err(invalid());
    }
    let Some(signature) =
        exact_signature_cache(store, global.declaration).map_err(|()| invalid())?
    else {
        return Ok(None);
    };
    let (Some(value_type), Some(instance_type)) = (value_type, instance_type) else {
        return Err(invalid());
    };
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = value.data() else {
        return Err(invalid());
    };
    let instance = store.type_payload(instance_type).ok_or_else(invalid)?;
    let record = store.signature(signature).ok_or_else(invalid)?;
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || interface.reference.object.structured.signatures.is_none()
            && interface.reference.object.structured.call_signature_count != 0
        || instance.flags() != TypeFlags::OBJECT
        || !instance.object_flags().contains(ObjectFlags::INTERFACE)
        || instance.symbol() != Some(plan.resolved_symbol)
        || instance.alias().is_some()
        || record.declaration() != Some(global.declaration)
        || record.flags() != SignatureFlags::CONSTRUCT
        || !record.parameters().is_empty()
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != Some(instance_type)
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store
            .callable_signature_parameter_types(signature)
            .is_some_and(|types| !types.is_empty())
        || store
            .function_signature_return_annotation(signature)
            .is_some_and(|annotation| annotation != (global.return_annotation, false))
        || authenticated_global_date_constructor_return(store, signature) != Some(instance_type)
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }

    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    }))
}

/// Authenticates a published zero-argument Date return without resolving its members.
#[allow(clippy::too_many_lines)] // Global symbols, source ownership, and signature caches form one proof.
pub(super) fn authenticated_global_date_constructor_return(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
) -> Option<TypeId> {
    let record = store.signature(signature)?;
    let declaration = record.declaration()?;
    let SourceNodeParent::Parent(owner_declaration) = store.source_node_parent(declaration)? else {
        return None;
    };
    let bootstrap = store.intrinsic_bootstrap()?;
    let globals = store.symbol_table(bootstrap.globals)?;
    let date = globals
        .get_source("Date")
        .and_then(|symbol| store.get_merged_symbol(symbol))?;
    let owner = globals
        .get_source("DateConstructor")
        .and_then(|symbol| store.get_merged_symbol(symbol))?;
    let date_record = store.symbol(date)?;
    let value_declaration = date_record.value_declaration()?;
    let value_annotation = store.source_direct_type_annotation(value_declaration)?;
    let value_name = NodeRef::new(
        value_annotation.arena,
        value_annotation.file,
        ts_ast::NodeId::new(u32::try_from(value_annotation.node.index().checked_sub(1)?).ok()?),
    );
    let owner_record = store.symbol(owner)?;
    let instance = store.declared_type_links(date)?.declared_type?;
    let constructor = store.declared_type_links(owner)?.declared_type?;
    for provider in [date, owner] {
        if store.declared_type_initialization_in_progress(provider)
            || preflight_class_or_interface_reference(
                store,
                &DeclaredTypeHost::default(),
                provider,
                store.symbol(provider)?.flags(),
            )
            .ok()
                != Some(0)
        {
            return None;
        }
    }
    let instance_record = store.type_payload(instance)?;
    let constructor_record = store.type_payload(constructor)?;
    let TypeData::Interface(interface) = constructor_record.data() else {
        return None;
    };
    let constructor_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|symbol| store.get_merged_symbol(symbol))?;
    let symbol_record = store.symbol(constructor_symbol)?;
    let return_annotation = store.source_direct_type_annotation(declaration)?;
    let return_name = NodeRef::new(
        return_annotation.arena,
        return_annotation.file,
        ts_ast::NodeId::new(u32::try_from(return_annotation.node.index().checked_sub(1)?).ok()?),
    );
    // Parameter nodes precede the return reference in parser order.
    let before_return_name = return_name
        .node
        .index()
        .checked_sub(1)
        .and_then(|index| u32::try_from(index).ok())
        .map(|index| {
            NodeRef::new(
                declaration.arena,
                declaration.file,
                ts_ast::NodeId::new(index),
            )
        });
    let allowed_date_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;

    if date_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || !date_record
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || date_record.flags().without(allowed_date_flags) != SymbolFlags::NONE
        || date_record.check_flags() != CheckFlags::NONE
        || date_record.name().as_utf8() != Some("Date")
        || date_record.parent().is_some()
        || date_record.exports().is_some()
        || date_record.export_symbol().is_some()
        || store.source_node_kind(value_declaration) != Some(SyntaxKind::VariableDeclaration)
        || store.source_node_kind(value_annotation) != Some(SyntaxKind::TypeReference)
        || store.source_node_parent(value_name) != Some(SourceNodeParent::Parent(value_annotation))
        || store.source_identifier_text(value_name) != Some("DateConstructor")
        || store.value_symbol_links(date)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(constructor),
                ..ValueSymbolLinks::default()
            })
        || store.type_node_links(value_annotation)
            != Some(&TypeNodeLinks {
                resolved_type: Some(constructor),
                ..TypeNodeLinks::default()
            })
        || store.symbol_node_links(value_annotation)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(owner),
            })
        || owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("DateConstructor")
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&owner_declaration))
        || store.source_node_kind(owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || symbol_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::SIGNATURE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || symbol_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || store.source_node_kind(declaration) != Some(SyntaxKind::ConstructSignature)
        || store.signature_links(declaration)
            != Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        || instance_record.flags() != TypeFlags::OBJECT
        || !instance_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || instance_record.symbol() != Some(date)
        || instance_record.alias().is_some()
        || constructor_record.flags() != TypeFlags::OBJECT
        || !constructor_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || constructor_record.symbol() != Some(owner)
        || constructor_record.alias().is_some()
        || record.flags() != SignatureFlags::CONSTRUCT
        || !record.parameters().is_empty()
        || !record.type_parameters().is_empty()
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != Some(instance)
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.source_node_kind(return_annotation) != Some(SyntaxKind::TypeReference)
        || store.source_node_kind(return_name) != Some(SyntaxKind::Identifier)
        || store.source_identifier_text(return_name) != Some("Date")
        || store.source_node_parent(return_name)
            != Some(SourceNodeParent::Parent(return_annotation))
        || before_return_name.is_some_and(|node| {
            store.source_node_parent(node) == Some(SourceNodeParent::Parent(declaration))
        })
        || store.type_node_links(return_annotation)
            != Some(&TypeNodeLinks {
                resolved_type: Some(instance),
                ..TypeNodeLinks::default()
            })
        || store.symbol_node_links(return_annotation)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(date),
            })
        || store.function_signature_return_annotation(signature) != Some((return_annotation, false))
        || store
            .callable_signature_parameter_types(signature)
            .is_some_and(|parameters| !parameters.is_empty())
        || interface.reference.object.structured.signatures.is_none()
            && interface.reference.object.structured.call_signature_count != 0
        || interface
            .reference
            .object
            .structured
            .signatures
            .as_deref()
            .is_some_and(|signatures| {
                signatures
                    .get(interface.reference.object.structured.call_signature_count..)
                    .is_none_or(|constructors| !constructors.contains(&signature))
            })
    {
        return None;
    }

    Some(instance)
}

fn resolved_global_promise_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalPromiseConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let Some(value_type) = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    if exact_type_cache(store, global.annotation)
        .map_err(|()| invalid())?
        .is_some_and(|cached| cached != value_type)
        || exact_class_value_type(store, plan.resolved_symbol)?
            .is_some_and(|cached| cached != value_type)
    {
        return Err(invalid());
    }
    let Some(promise_target) = store
        .declared_type_links(plan.resolved_symbol)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    let Some(base) = exact_signature_cache(store, global.declaration).map_err(|()| invalid())?
    else {
        return Ok(None);
    };
    let generic = store
        .declared_type_links(global.type_parameter)
        .and_then(|links| links.declared_type)
        .ok_or_else(invalid)?;
    let executor = exact_type_cache(store, global.parameter_annotation)
        .map_err(|()| invalid())?
        .ok_or_else(invalid)?;
    let return_type = exact_type_cache(store, global.return_annotation)
        .map_err(|()| invalid())?
        .ok_or_else(invalid)?;
    let record = store.signature(base).ok_or_else(invalid)?;
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
        || record.flags() != SignatureFlags::CONSTRUCT
        || record.declaration() != Some(global.declaration)
        || record.type_parameters() != [generic]
        || record.parameters() != [global.parameter]
        || record.min_argument_count() != 1
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != Some(return_type)
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || exact_class_value_type(store, global.parameter)? != Some(executor)
        || store.function_signature_return_annotation(base)
            != Some((global.return_annotation, false))
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            base,
        )));
    }
    let unknown = store
        .intrinsic_bootstrap()
        .ok_or_else(invalid)?
        .unknown_type;
    let selected = match store.cached_signature(base, type_list_key(&[unknown]), &[unknown]) {
        CachedSignatureLookup::Hit(signature) => signature,
        CachedSignatureLookup::Missing => return Ok(None),
        CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
            return Err(invalid());
        }
    };
    let signature = store.signature(selected).ok_or_else(invalid)?;
    let instance_type = signature.resolved_return_type().ok_or_else(invalid)?;
    let instance =
        validate_direct_generic_reference(store, instance_type).map_err(|_| invalid())?;
    if instance.target != promise_target
        || instance.type_arguments.as_slice() != [unknown]
        || signature.flags() != SignatureFlags::CONSTRUCT
        || signature.declaration() != Some(global.declaration)
        || !signature.type_parameters().is_empty()
        || signature.min_argument_count() != 1
        || signature.target() != Some(base)
        || signature.mapper().is_none()
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            selected,
        )));
    }

    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature: selected,
    }))
}

fn resolved_global_array_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    global: &SourceGlobalArrayConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    };
    let Some(value_type) = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    if exact_type_cache(store, global.annotation)
        .map_err(|()| invalid())?
        .is_some_and(|cached| cached != value_type)
        || exact_class_value_type(store, plan.resolved_symbol)?
            .is_some_and(|cached| cached != value_type)
    {
        return Err(invalid());
    }
    let value = store.type_payload(value_type).ok_or_else(invalid)?;
    if value.flags() != TypeFlags::OBJECT
        || !value.object_flags().contains(ObjectFlags::INTERFACE)
        || value.symbol() != Some(global.owner)
        || value.alias().is_some()
    {
        return Err(invalid());
    }
    let selected = match global.selection {
        SourceGlobalArraySelection::Length => global.length,
        SourceGlobalArraySelection::GenericLength(_) => global.generic_length,
        SourceGlobalArraySelection::Items(_) => global.items,
    };
    let Some(base) = exact_signature_cache(store, selected.declaration).map_err(|()| invalid())?
    else {
        return Ok(None);
    };
    let base_record = store.signature(base).ok_or_else(invalid)?;
    let is_rest = matches!(global.selection, SourceGlobalArraySelection::Items(_));
    let expected_minimum = i32::from(matches!(
        global.selection,
        SourceGlobalArraySelection::GenericLength(_)
    ));
    let expected_type_parameters = usize::from(selected.type_parameter.is_some());
    if base_record.declaration() != Some(selected.declaration)
        || !base_record.flags().contains(SignatureFlags::CONSTRUCT)
        || base_record
            .flags()
            .contains(SignatureFlags::HAS_REST_PARAMETER)
            != is_rest
        || base_record.parameters() != [selected.parameter]
        || base_record.min_argument_count() != expected_minimum
        || base_record.resolved_min_argument_count() != -1
        || base_record.type_parameters().len() != expected_type_parameters
        || base_record.this_parameter().is_some()
        || base_record.resolved_type_predicate().is_some()
        || base_record.target().is_some()
        || base_record.mapper().is_some()
        || base_record.composite().is_some()
        || store
            .value_symbol_links(selected.parameter)
            .and_then(|links| links.resolved_type)
            .is_none()
        || store
            .function_signature_return_annotation(base)
            .is_some_and(|annotation| annotation != (selected.return_annotation, false))
    {
        return Err(invalid());
    }

    let (signature, element) = match global.selection {
        SourceGlobalArraySelection::Length => {
            let any = store.intrinsic_bootstrap().ok_or_else(invalid)?.any_type;
            (base, any)
        }
        SourceGlobalArraySelection::GenericLength(element)
        | SourceGlobalArraySelection::Items(element) => {
            let key = type_list_key(&[element]);
            match store.cached_signature(base, key, &[element]) {
                CachedSignatureLookup::Hit(signature) => (signature, element),
                CachedSignatureLookup::Missing => return Ok(None),
                CachedSignatureLookup::HashCollision(_) | CachedSignatureLookup::Invalid => {
                    return Err(invalid());
                }
            }
        }
    };
    let selected_record = store.signature(signature).ok_or_else(invalid)?;
    let instance_type = selected_record.resolved_return_type().ok_or_else(invalid)?;
    let instance = store.type_payload(instance_type).ok_or_else(invalid)?;
    let TypeData::TypeReference(reference) = instance.data() else {
        return Err(invalid());
    };
    if reference.object.target != Some(global.array_target)
        || reference.resolved_type_arguments.as_deref() != Some(&[element])
        || selected_record
            .flags()
            .contains(SignatureFlags::HAS_REST_PARAMETER)
            != is_rest
        || selected_record.min_argument_count() != expected_minimum
        || signature != base
            && (selected_record.target() != Some(base)
                || selected_record.mapper().is_none()
                || !selected_record.type_parameters().is_empty())
    {
        return Err(invalid());
    }

    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    }))
}

/// Rechecks the local/export attachment before a class construction can use cached results.
fn preflight_exported_constructor_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    let (symbol, declaration) = match &plan.target {
        SourceNewTarget::Class(class) => (class.symbol(), class.declaration()),
        SourceNewTarget::SourceClass(class) | SourceNewTarget::ConstructorOverloads(class) => {
            (class.symbol(), class.declaration())
        }
        SourceNewTarget::GenericSourceClass(generic) => {
            (generic.class.symbol(), generic.class.declaration())
        }
        _ => return Ok(()),
    };
    if plan.resolved_symbol == symbol {
        return Ok(());
    }
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(declaration));
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    if constructor_value_symbol(store, plan.constructor, plan.resolved_symbol)? != symbol
        || bound.local_symbol(declaration) != Some(plan.resolved_symbol)
        || bound.symbol(declaration) != Some(symbol)
    {
        return Err(invalid());
    }
    let NodeData::ClassDeclaration(class) = &host.node(declaration).ok_or_else(invalid)?.data
    else {
        return Err(invalid());
    };
    if class.type_parameters.is_some() && !plan.is_generic_source_class() {
        return Err(unsupported(SourceNewUnsupported::Constructor(
            plan.constructor,
        )));
    }
    match &plan.target {
        SourceNewTarget::Class(class) => {
            preflight_nongeneric_class_member_query(store, host, class)?;
        }
        SourceNewTarget::SourceClass(class) | SourceNewTarget::ConstructorOverloads(class) => {
            if !source_class_plan_is_current(store, host, class)? {
                return Err(invalid());
            }
        }
        SourceNewTarget::GenericSourceClass(generic) => {
            if !generic.class.has_generic_constructor()
                || !source_class_plan_is_current(store, host, &generic.class)?
            {
                return Err(invalid());
            }
        }
        _ => unreachable!("only local class targets have an exported constructor binding"),
    }
    Ok(())
}

#[cfg(test)]
fn preflight_default_new_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_default_new_cache_with_context(store, host, plan, None)
}

fn preflight_default_new_cache_with_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<(), SourceNewError> {
    preflight_exported_constructor_binding(store, host, plan)?;
    let constructor_symbol = exact_symbol_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    if constructor_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol) {
        return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        )));
    }
    let constructor_type = exact_type_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let result_type = exact_type_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let signature = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    if result_type.is_some() != signature.is_some() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    for argument in plan.arguments() {
        let cached = exact_type_cache(store, argument.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
        let expected = cached_argument_type(store, argument)?;
        if cached.is_some_and(|cached| Some(cached) != expected) {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument.node,
            )));
        }
    }
    for argument in &plan.type_arguments {
        if exact_type_cache(store, argument.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?
            .is_some_and(|cached| cached != argument.type_)
        {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument.node,
            )));
        }
    }

    match &plan.target {
        SourceNewTarget::Library(_) | SourceNewTarget::GenericLibrary(_) => {
            let (globals, options) = source_context.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?;
            let candidates = resolve_library_new_candidates(store, host, globals, options, plan)
                .map_err(|error| {
                    trace_constructor_failure(
                        "cache_read_error",
                        plan.node,
                        plan.constructor,
                        format_args!(
                            "cached_constructor_symbol={constructor_symbol:?} cached_constructor_type={constructor_type:?} cached_result_type={result_type:?} cached_signature={signature:?} error={error:?}"
                        ),
                    );
                    error
                })?;
            if plan.is_generic_library_constructor() {
                let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
                if constructor_type.is_some_and(|type_| {
                    candidates
                        .as_ref()
                        .is_none_or(|candidates| candidates.value_type != type_)
                }) {
                    return Err(invalid());
                }
                if let Some(signature) = signature {
                    let candidates = candidates.as_ref().ok_or_else(invalid)?;
                    if constructor_symbol != Some(plan.resolved_symbol)
                        || constructor_type != Some(candidates.value_type)
                        || store
                            .signature(signature)
                            .and_then(Signature::resolved_return_type)
                            != result_type
                    {
                        return Err(invalid());
                    }
                    preflight_generic_class_constructor_signature(
                        store,
                        candidates.value_type,
                        signature,
                        Some(CanonicalArrayTargets::from_global_types(globals)),
                    )
                    .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
                }
                preflight_library_argument_caches(store, host, globals, options, plan)?;
                return Ok(());
            }
            if constructor_type.is_some_and(|type_| {
                candidates
                    .as_ref()
                    .is_none_or(|candidates| candidates.value_type != type_)
            }) || signature.is_some_and(|signature| {
                candidates.as_ref().is_none_or(|candidates| {
                    !candidates.callables.iter().any(|candidate| {
                        candidate.signature == signature && candidate.return_type == result_type
                    })
                })
            }) || signature.is_some()
                && (constructor_symbol != Some(plan.resolved_symbol) || constructor_type.is_none())
            {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
            preflight_library_argument_caches(store, host, globals, options, plan)?;
        }
        SourceNewTarget::GenericSourceClass(generic) => {
            let invalid = || invariant(SourceNewInvariant::InvalidExpressionCache(plan.node));
            preflight_generic_source_class_plan(store, host, plan, generic)?;
            let members = super::classes::completed_source_class_constructors(
                store,
                host,
                generic.class.symbol(),
            )?;
            if constructor_type.is_some_and(|constructor| {
                members
                    .as_ref()
                    .is_none_or(|members| members.members().shells().value_type() != constructor)
            }) {
                return Err(invalid());
            }
            if let Some(signature) = signature {
                let members = members.as_ref().ok_or_else(invalid)?;
                let value = members.members().shells().value_type();
                let targets = generic
                    .class
                    .type_query_context()
                    .ok_or_else(invalid)?
                    .array_targets();
                if constructor_symbol != Some(plan.resolved_symbol)
                    || constructor_type != Some(value)
                    || store
                        .signature(signature)
                        .and_then(Signature::resolved_return_type)
                        != result_type
                {
                    return Err(invalid());
                }
                if store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| signature == bootstrap.unknown_signature)
                {
                    // Source execution repeats the access proof with its actual body token.
                    generic_new_error_signature(store, plan.node)?;
                } else {
                    preflight_generic_class_constructor_signature(
                        store,
                        value,
                        signature,
                        Some(targets),
                    )
                    .map_err(|error| generic_constructor_error(plan.node, error.into()))?;
                }
            }
        }
        SourceNewTarget::ConstructorOverloads(class) => {
            let group =
                super::classes::source_class_constructor_overloads(store, host, class.symbol())?;
            if constructor_type.is_some_and(|type_| {
                group
                    .as_ref()
                    .is_none_or(|group| group.members.shells().value_type() != type_)
            }) || result_type.is_some_and(|type_| {
                group
                    .as_ref()
                    .is_none_or(|group| group.members.shells().instance_type() != type_)
            }) || signature.is_some_and(|signature| {
                group.as_ref().is_none_or(|group| {
                    !group
                        .signatures
                        .iter()
                        .any(|candidate| candidate.signature == signature)
                })
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::SourceClass(class) => {
            let resolved = resolved_source_class_constructor(store, host, plan, class)?;
            let candidates = if class.has_public_inherited_constructor() && resolved.is_some() {
                super::classes::source_class_expression_constructor_candidates(
                    store,
                    host,
                    class.symbol(),
                )?
            } else {
                None
            };
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                candidates.as_ref().map_or_else(
                    || resolved.is_none_or(|resolved| signature != resolved.signature),
                    |candidates| {
                        !candidates
                            .iter()
                            .any(|callable| callable.signature == signature)
                    },
                )
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::Class(class) => {
            let instance = store
                .declared_type_links(class.symbol())
                .and_then(|links| links.declared_type);
            let value = exact_class_value_type(store, class.symbol())?;
            if constructor_type.is_some_and(|constructor| Some(constructor) != value)
                || result_type.is_some_and(|result| Some(result) != instance)
            {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
            if let (Some(value), Some(instance), Some(signature)) = (value, instance, signature) {
                validate_selected_default_signature(
                    store, host, plan, class, value, instance, signature,
                )?;
            } else if signature.is_some() {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::ImportedClass(binding) => {
            if store
                .alias_symbol_links(binding.alias_symbol)
                .and_then(|links| links.alias_target.symbol())
                .is_none()
            {
                if constructor_type.is_some() || result_type.is_some() || signature.is_some() {
                    return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                        plan.node,
                    )));
                }
                return Ok(());
            }
            let class = imported_constructor_class(store, host, plan, binding)?;
            let value = exact_class_value_type(store, class.symbol())?;
            if constructor_type.is_some_and(|constructor| Some(constructor) != value) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
            let resolved = resolved_imported_constructor(store, host, plan, &class)?;
            if result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::Declared(declared) => {
            let resolved = resolved_declared_constructor(store, plan, declared)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::ClassUnion(union) => {
            let candidates = class_union_constructor_candidates(store, plan, union)?;
            let resolved = resolved_declared_class_union_constructor(store, plan, union)?;
            if constructor_type.is_some_and(|constructor| {
                candidates
                    .as_ref()
                    .is_none_or(|candidates| constructor != candidates.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::GlobalObject(global) => {
            let resolved = resolved_global_object_constructor(store, plan, global)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::GlobalArray(global) => {
            let resolved = resolved_global_array_constructor(store, plan, global)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::GlobalDate(global) => {
            let resolved = resolved_global_date_constructor(store, plan, global)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::DeclaredInterface(declared) => {
            let resolved = global_error::resolve(store, host, plan, declared)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
        SourceNewTarget::GlobalPromise(global) => {
            let resolved = resolved_global_promise_constructor(store, plan, global)?;
            if constructor_type.is_some_and(|constructor| {
                resolved.is_none_or(|resolved| constructor != resolved.value_type)
            }) || result_type.is_some_and(|result| {
                resolved.is_none_or(|resolved| result != resolved.instance_type)
            }) || signature.is_some_and(|signature| {
                resolved.is_none_or(|resolved| signature != resolved.signature)
            }) {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    plan.node,
                )));
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn preflight_publication_cache_with_context(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
    argument_types: &[TypeId],
    source_context: Option<(&CanonicalGlobalTypes, CanonicalCheckerOptions)>,
) -> Result<(), SourceNewError> {
    preflight_prepared_default_new_cache_with_context(store, host, plan, source_context)?;
    let constructor_symbol = exact_symbol_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let constructor = exact_type_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let result = exact_type_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let selected = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    if plan.argument_nodes().count() != argument_types.len() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    for (argument, argument_type) in plan.arguments().zip(argument_types) {
        let cached = exact_type_cache(store, argument.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
        if cached.is_some_and(|cached| cached != *argument_type)
            || cached_argument_type(store, argument)? != Some(*argument_type)
        {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument.node,
            )));
        }
    }
    if let Some(arguments) = plan.checked_expression_arguments() {
        for (argument, &argument_type) in arguments.iter().zip(argument_types) {
            if exact_type_cache(store, argument.node).map_err(|()| {
                invariant(SourceNewInvariant::InvalidExpressionCache(argument.node))
            })? != Some(argument_type)
            {
                return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    argument.node,
                )));
            }
        }
    }
    if constructor_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
        || constructor.is_some_and(|type_| type_ != value_type)
        || result.is_some_and(|type_| type_ != instance_type)
        || selected.is_some_and(|selected| selected != signature)
        || result.is_some() != selected.is_some()
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    Ok(())
}

fn cached_argument_type(
    store: &CanonicalTypeMapperStore,
    argument: &SourceNewArgument,
) -> Result<Option<TypeId>, SourceNewError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
    let regular = match &argument.value {
        SourceNewArgumentValue::String(value) => bootstrap.cached_string_literal_type(value),
        SourceNewArgumentValue::Number(value) => bootstrap.cached_number_literal_type(*value),
        SourceNewArgumentValue::Boolean(value) => Some(if *value {
            bootstrap.regular_true_type
        } else {
            bootstrap.regular_false_type
        }),
        SourceNewArgumentValue::EmptyObject(object) => {
            return object_literal_state(store, object)
                .map(|state| {
                    state
                        .filter(|state| state.is_resolved())
                        .map(PropertyObjectState::type_id)
                })
                .map_err(|_| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)));
        }
    };
    let Some(regular) = regular else {
        return Ok(None);
    };
    store
        .validate_union_constituent(regular)
        .map_err(|error| literal_cache_error(argument.node, error))?;
    let Some(TypeData::Literal(literal)) = store.type_payload(regular).map(TypeRecord::data) else {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            argument.node,
        )));
    };
    let matches_value = match (&argument.value, &literal.value) {
        (SourceNewArgumentValue::String(expected), LiteralValue::String(actual)) => {
            expected == actual
        }
        (SourceNewArgumentValue::Number(expected), LiteralValue::Number(actual)) => {
            expected == actual
        }
        (SourceNewArgumentValue::Boolean(expected), LiteralValue::Boolean(actual)) => {
            expected == actual
        }
        _ => false,
    };
    if !matches_value || literal.regular_type != regular {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            argument.node,
        )));
    }
    // Bootstrap literals can exist before expression checking creates their fresh type.
    if literal.fresh_type.is_none() {
        return Ok(None);
    }
    store
        .fresh_type_of_literal_type(regular)
        .map(Some)
        .map_err(|error| literal_cache_error(argument.node, error))
}

fn literal_cache_error(node: NodeRef, error: LiteralTypeCacheError) -> SourceNewError {
    if error == LiteralTypeCacheError::Capacity {
        invariant(SourceNewInvariant::Capacity(node))
    } else {
        invariant(SourceNewInvariant::InvalidExpressionCache(node))
    }
}

fn exact_symbol_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<SemanticSymbolId>, ()> {
    match store.symbol_node_links(node) {
        None => Ok(None),
        Some(links) if links == &SymbolNodeLinks::default() => Ok(None),
        Some(links) => {
            let symbol = links.resolved_symbol.ok_or(())?;
            (links
                == &(SymbolNodeLinks {
                    resolved_symbol: Some(symbol),
                })
                && store.symbol(symbol).is_some())
            .then_some(Some(symbol))
            .ok_or(())
        }
    }
}

fn exact_type_cache(store: &CanonicalTypeMapperStore, node: NodeRef) -> Result<Option<TypeId>, ()> {
    match store.type_node_links(node) {
        None => Ok(None),
        Some(links) if links == &TypeNodeLinks::default() => Ok(None),
        Some(links) => {
            let type_ = links.resolved_type.ok_or(())?;
            (links
                == &(TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                })
                && store.type_payload(type_).is_some())
            .then_some(Some(type_))
            .ok_or(())
        }
    }
}

fn exact_signature_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<SignatureId>, ()> {
    match store.signature_links(node) {
        None => Ok(None),
        Some(links) if links == &SignatureLinks::default() => Ok(None),
        Some(links) => {
            let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
                return Err(());
            };
            (links
                == &(SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
                && store.signature(signature).is_some())
            .then_some(Some(signature))
            .ok_or(())
        }
    }
}

fn exact_class_value_type(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, SourceNewError> {
    match store.value_symbol_links(symbol) {
        None => Ok(None),
        Some(links) if links == &ValueSymbolLinks::default() => Ok(None),
        Some(links) => {
            let type_ = links
                .resolved_type
                .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(symbol)))?;
            (links
                == &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
                && store.type_payload(type_).is_some())
            .then_some(Some(type_))
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(symbol)))
        }
    }
}

fn validate_selected_default_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
) -> Result<(), SourceNewError> {
    let parameter = if plan.is_imported_class() {
        imported_constructor_parameter(store, host, plan, class)?
    } else {
        plan.parameter
    };
    let TypeData::Interface(instance) = store
        .type_payload(instance_type)
        .map(super::type_records::TypeRecord::data)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(class.symbol())))?
    else {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            class.symbol(),
        )));
    };
    let type_parameters = instance
        .reference
        .resolved_type_arguments
        .as_deref()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(class.symbol())))?;
    let value = store
        .type_payload(value_type)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(class.symbol())))?;
    let Some(structured) = value.data().structured() else {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            class.symbol(),
        )));
    };
    if structured.call_signature_count != 0
        || structured.signatures.as_deref() != Some(&[signature])
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    let signature_record = store
        .signature(signature)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidConstructSignature(signature)))?;
    let expected_flags = SignatureFlags::CONSTRUCT
        | if class.is_abstract() {
            SignatureFlags::ABSTRACT
        } else {
            SignatureFlags::NONE
        };
    if signature_record.flags() != expected_flags
        || signature_record.declaration() != class.constructor_declaration()
        || signature_record.type_parameters() != type_parameters
        || signature_record.parameters() != class.constructor_parameter_symbols().as_slice()
        || signature_record.this_parameter().is_some()
        || signature_record.min_argument_count() != class.constructor_minimum_argument_count()
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.resolved_return_type() != Some(instance_type)
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    if let Some(parameter) = parameter {
        let invalid = || invariant(SourceNewInvariant::InvalidConstructSignature(signature));
        let declaration = store
            .symbol(parameter.symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or_else(invalid)?;
        let NodeData::ParameterDeclaration(data) =
            &host.node(declaration).ok_or_else(invalid)?.data
        else {
            return Err(invalid());
        };
        let value_type = optional_constructor_parameter_type(
            store,
            parameter.type_,
            data.question_token.is_some(),
            declaration,
        )?
        .ok_or_else(invalid)?;
        if store.value_symbol_links(parameter.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(value_type),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(invalid());
        }
    }
    if class.constructor_annotation().is_some() {
        let invalid = || invariant(SourceNewInvariant::InvalidConstructSignature(signature));
        let symbol = class.constructor_parameter_symbol().ok_or_else(invalid)?;
        let type_ = class
            .annotated_constructor_parameter_type(store, host)?
            .ok_or_else(invalid)?;
        if store.value_symbol_links(symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(invalid());
        }
    }
    if instance.reference.object.target != Some(instance_type) {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            class.symbol(),
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SourceCheckError, UnsupportedSourceSyntax,
        classes::{ClassHeritageMembersValidation, validate_class_heritage_members},
        production::GlobalMergeCompletion,
    };

    const LIBRARY_EXPRESSION_NEW_DECLARATIONS: &str = concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "interface BuildResult { value: string; } ",
        "interface OtherResult { value: number; } ",
        "declare var BuildValue: { prototype: BuildResult; ",
        "new(): BuildResult; new(value?: number): OtherResult; empty(): BuildResult; };",
    );

    #[allow(clippy::too_many_arguments)]
    fn library_zero_argument_plan(
        source: &ParseResult,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        options: CanonicalCheckerOptions,
        node: NodeRef,
    ) -> SourceDefaultNewPlan {
        let mut plan = plan_direct_default_new_with_source_context(
            &source.arena,
            bound,
            store,
            host,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            node,
            false,
            globals,
            options,
        )
        .unwrap();
        assert!(plan.is_library_constructor());
        assert_eq!(plan.expression_argument_nodes(), Some(&[][..]));
        plan.set_expression_arguments(Vec::new()).unwrap();
        plan
    }

    #[test]
    fn library_expression_new_revalidates_complete_candidates_and_saved_pairs() {
        let library = parse_source_file(LIBRARY_EXPRESSION_NEW_DECLARATIONS);
        let source = parse_source_file("const value = new BuildValue();");
        assert!(library.diagnostics.is_empty());
        assert!(source.diagnostics.is_empty());
        for damage in 0..9 {
            let library_file = FileId::new(202_800);
            let file = FileId::new(202_801);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, file);
            context.check_source_file(file).unwrap();
            assert!(context.diagnostics().is_empty());
            let library_bound = context.file(library_file).unwrap().1.clone();
            let source_bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [
                    (&library.arena, &library_bound),
                    (&source.arena, &source_bound),
                ],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let globals = context.global_types().clone();
            let options = context.options();
            let (node, constructor) = variable_new(&source, file, "value");
            let plan = library_zero_argument_plan(
                &source,
                &source_bound,
                context.store(),
                &host,
                &globals,
                options,
                node,
            );
            let candidates = source_library_constructor_candidates(
                context.store(),
                &host,
                &globals,
                options,
                &plan,
            )
            .unwrap();
            assert_eq!(candidates.callables.len(), 2);
            assert_ne!(
                candidates.callables[0].return_type,
                candidates.callables[1].return_type
            );
            let selected = candidates.callables[0].signature;
            let later = candidates.callables[1].signature;
            let return_type = candidates.callables[0].return_type.unwrap();
            let other_return = candidates.callables[1].return_type.unwrap();
            assert_eq!(
                exact_signature_cache(context.store(), node),
                Ok(Some(selected))
            );
            assert_eq!(
                exact_type_cache(context.store(), node),
                Ok(Some(return_type))
            );
            let parameter = context.store().signature(later).unwrap().parameters()[0];
            let original_parameter = context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .clone();
            let original_symbol = context
                .store()
                .symbol_node_links(constructor)
                .unwrap()
                .clone();
            let original_constructor = context
                .store()
                .type_node_links(constructor)
                .unwrap()
                .clone();
            let original_result = context.store().type_node_links(node).unwrap().clone();
            let original_signature = context.store().signature_links(node).unwrap().clone();
            let original_members = context
                .store()
                .type_payload(candidates.value_type)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .clone();
            let owner = context
                .store()
                .type_payload(return_type)
                .and_then(TypeRecord::symbol)
                .unwrap();
            let primitive = context.store().intrinsic_bootstrap().unwrap().string_type;
            let before = format!("{:?}", context.store());
            preflight_direct_default_new_with_source_context(
                context.store(),
                &host,
                &globals,
                options,
                &plan,
            )
            .unwrap();
            assert_eq!(format!("{:?}", context.store()), before);

            let store = context.store_mut_for_test();
            match damage {
                0 => assert!(store.set_symbol_node_links(
                    constructor,
                    SymbolNodeLinks {
                        resolved_symbol: Some(owner)
                    }
                )),
                1 => assert!(store.set_type_node_links(
                    constructor,
                    TypeNodeLinks {
                        resolved_type: Some(primitive),
                        ..TypeNodeLinks::default()
                    }
                )),
                2 => assert!(store.set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(other_return),
                        ..TypeNodeLinks::default()
                    }
                )),
                3 => assert!(store.set_signature_links(
                    node,
                    SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolved(later),
                        ..SignatureLinks::default()
                    }
                )),
                4 => assert!(store.set_type_node_links(node, TypeNodeLinks::default())),
                5 => assert!(store.set_signature_links(node, SignatureLinks::default())),
                6 => assert!(store.set_signature_resolved_return_type(later, Some(return_type))),
                7 => assert!(store.set_value_symbol_links(
                    parameter,
                    ValueSymbolLinks {
                        resolved_type: Some(primitive),
                        ..original_parameter.clone()
                    }
                )),
                8 => assert!(store.set_structured_type_members(
                    candidates.value_type,
                    original_members.members,
                    original_members.properties.clone(),
                    Some(Vec::new()),
                    Some(vec![later, selected]),
                    original_members.index_infos.clone(),
                )),
                _ => unreachable!(),
            }
            let damaged = format!("{store:?}");
            let mut session = InstantiationSession::new(Default::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            for _ in 0..2 {
                assert!(matches!(
                    preflight_direct_default_new_with_source_context(
                        store, &host, &globals, options, &plan
                    ),
                    Err(SourceNewError::Invariant(_)) | Err(SourceNewError::DeclaredType(_)),
                ));
                assert!(
                    prepare_direct_default_news(
                        store,
                        &host,
                        &globals,
                        options,
                        &mut session,
                        &mut diagnostics,
                        std::slice::from_ref(&plan),
                    )
                    .is_err()
                );
                assert_eq!(format!("{store:?}"), damaged);
                assert_eq!(
                    (
                        session.query_count(),
                        session.total_count(),
                        session.limit_event_count()
                    ),
                    (0, 0, 0)
                );
                assert!(diagnostics.is_empty());
            }
            match damage {
                0 => assert!(store.set_symbol_node_links(constructor, original_symbol)),
                1 => assert!(store.set_type_node_links(constructor, original_constructor)),
                2 | 4 => assert!(store.set_type_node_links(node, original_result)),
                3 | 5 => assert!(store.set_signature_links(node, original_signature)),
                6 => assert!(store.set_signature_resolved_return_type(later, Some(other_return))),
                7 => assert!(store.set_value_symbol_links(parameter, original_parameter)),
                8 => assert!(store.set_structured_type_members(
                    candidates.value_type,
                    original_members.members,
                    original_members.properties.clone(),
                    Some(Vec::new()),
                    original_members.signatures.clone(),
                    original_members.index_infos.clone(),
                )),
                _ => unreachable!(),
            }
            let restored = format!("{store:?}");
            let checked = super::super::source_calls::check_source_library_expression_new(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                &[],
            )
            .unwrap();
            assert_eq!(checked.signature, selected);
            assert_eq!(checked.instance_type, return_type);
            assert_eq!(checked.value_type, candidates.value_type);
            assert_eq!(format!("{store:?}"), restored);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn library_expression_new_batch_preflights_later_nodes_before_preparation() {
        let library = parse_source_file(LIBRARY_EXPRESSION_NEW_DECLARATIONS);
        let source =
            parse_source_file("const first = new BuildValue(); const second = new BuildValue();");
        let library_file = FileId::new(202_802);
        let file = FileId::new(202_803);
        let mut context = global_object_constructor_context(&library, &source, library_file, file);
        let library_bound = context.file(library_file).unwrap().1.clone();
        let source_bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let first = variable_new(&source, file, "first").0;
        let (second, constructor) = variable_new(&source, file, "second");
        let plans = [first, second].map(|node| {
            library_zero_argument_plan(
                &source,
                &source_bound,
                context.store(),
                &host,
                &globals,
                options,
                node,
            )
        });
        let value_symbol = plans[0].resolved_symbol();
        let foreign = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let store = context.store_mut_for_test();
        assert!(store.set_symbol_node_links(
            constructor,
            SymbolNodeLinks {
                resolved_symbol: Some(foreign)
            }
        ));
        let damaged = format!("{store:?}");
        let mut session = InstantiationSession::new(Default::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        for _ in 0..2 {
            assert_eq!(
                prepare_direct_default_news(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plans,
                ),
                Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    constructor
                )))
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert!(
                store
                    .value_symbol_links(value_symbol)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            assert!(store.type_node_links(first).is_none());
            assert!(store.signature_links(first).is_none());
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (0, 0, 0)
            );
            assert!(diagnostics.is_empty());
        }
        assert!(store.set_symbol_node_links(constructor, SymbolNodeLinks::default()));
        prepare_direct_default_news(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plans,
        )
        .unwrap();
        for plan in &plans {
            let checked = super::super::source_calls::check_source_library_expression_new(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                plan,
                &[],
            )
            .unwrap();
            assert_eq!(
                exact_signature_cache(store, plan.node),
                Ok(Some(checked.signature))
            );
            assert_eq!(
                exact_type_cache(store, plan.node),
                Ok(Some(checked.instance_type))
            );
        }
        let warm = format!("{store:?}");
        prepare_direct_default_news(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plans,
        )
        .unwrap();
        assert_eq!(format!("{store:?}"), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn library_expression_new_keeps_current_array_authority_on_warm_reads() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface BuildResult { value: string; } ",
            "declare var BuildValue: { prototype: BuildResult; ",
            "new(values?: string[]): BuildResult; };",
        ));
        let source = parse_source_file("const value = new BuildValue();");
        let library_file = FileId::new(202_804);
        let file = FileId::new(202_805);
        let mut context = global_object_constructor_context(&library, &source, library_file, file);
        context.check_source_file(file).unwrap();
        let library_bound = context.file(library_file).unwrap().1.clone();
        let source_bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let (node, _) = variable_new(&source, file, "value");
        let plan = library_zero_argument_plan(
            &source,
            &source_bound,
            context.store(),
            &host,
            &globals,
            options,
            node,
        );
        let candidates =
            source_library_constructor_candidates(context.store(), &host, &globals, options, &plan)
                .unwrap();
        let [callable] = candidates.callables.as_slice() else {
            panic!("one real constructor")
        };
        let array = callable.parameters[0];
        let reference = context
            .store()
            .canonical_array_reference(&globals, array)
            .unwrap()
            .unwrap();
        assert_eq!(
            reference.element_type,
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        let TypeData::TypeReference(record) = context
            .store()
            .type_payload(reference.base_type)
            .unwrap()
            .data()
        else {
            panic!("real canonical Array reference")
        };
        assert_eq!(record.object.target, Some(globals.array_type));
        let other = global_object_constructor_context(
            &library,
            &source,
            FileId::new(202_806),
            FileId::new(202_807),
        );
        let mut missing = globals.clone();
        missing.array_type = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_generic_type;
        let mut foreign = globals.clone();
        foreign.array_type = other.global_types().array_type;
        for invalid_globals in [&missing, &foreign] {
            let before = format!("{:?}", context.store());
            let mut session = InstantiationSession::new(Default::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            for _ in 0..2 {
                assert!(
                    preflight_direct_default_new_with_source_context(
                        context.store(),
                        &host,
                        invalid_globals,
                        options,
                        &plan,
                    )
                    .is_err()
                );
                assert!(
                    prepare_direct_default_news(
                        context.store_mut_for_test(),
                        &host,
                        invalid_globals,
                        options,
                        &mut session,
                        &mut diagnostics,
                        std::slice::from_ref(&plan),
                    )
                    .is_err()
                );
                assert_eq!(format!("{:?}", context.store()), before);
                assert_eq!(
                    (
                        session.query_count(),
                        session.total_count(),
                        session.limit_event_count()
                    ),
                    (0, 0, 0)
                );
                assert!(diagnostics.is_empty());
            }
        }
        let before = format!("{:?}", context.store());
        assert_eq!(
            source_library_constructor_candidates(context.store(), &host, &globals, options, &plan),
            Ok(candidates)
        );
        assert_eq!(format!("{:?}", context.store()), before);
    }

    #[test]
    fn library_expression_new_preparation_uses_the_spent_source_caller() {
        use crate::semantic::{
            array_types::CanonicalArrayTargets,
            instantiate::{InstantiationLimits, instantiate_type_with_vector_and_session},
        };
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface BuildResult { value: string; } ",
            "type Payload<T> = T[]; ",
            "declare var BuildValue: { prototype: BuildResult; ",
            "new(values?: Payload<string>): BuildResult; };",
        ));
        let source = parse_source_file("const value = new BuildValue();");
        let library_file = FileId::new(202_808);
        let file = FileId::new(202_809);
        let mut context = global_object_constructor_context(&library, &source, library_file, file);
        let library_bound = context.file(library_file).unwrap().1.clone();
        let source_bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let (node, constructor) = variable_new(&source, file, "value");
        let plan = library_zero_argument_plan(
            &source,
            &source_bound,
            context.store(),
            &host,
            &globals,
            options,
            node,
        );
        let parameter_node = library
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &library.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == "Payload").then_some(NodeRef::new(
                    library.arena.id(),
                    library_file,
                    alias.type_parameters.as_ref()?.nodes[0],
                ))
            })
            .unwrap();
        let parameter_symbol = library_bound.symbol(parameter_node).unwrap();
        let store = context.store_mut_for_test();
        let parameter = execute_type_parameter(store, parameter_symbol);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut caller = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                parameter,
                &[parameter],
                &[number],
                Some(CanonicalArrayTargets::from_global_types(&globals)),
                &mut caller,
            ),
            Ok(number)
        );
        assert_eq!(
            (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_count()
            ),
            (1, 1, 0)
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            prepare_direct_default_news(
                store,
                &host,
                &globals,
                options,
                &mut caller,
                &mut diagnostics,
                std::slice::from_ref(&plan),
            )
            .is_err()
        );
        assert_eq!(
            (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_count()
            ),
            (1, 1, 1)
        );
        assert_eq!(exact_type_cache(store, constructor), Ok(None));
        assert_eq!(exact_type_cache(store, node), Ok(None));
        assert_eq!(exact_signature_cache(store, node), Ok(None));
        assert!(
            store
                .value_symbol_links(plan.resolved_symbol())
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn library_expression_new_preflights_nested_literal_facts_without_semantic_replay() {
        use crate::semantic::source::PlannedObjectMember;
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface BuildResult { value: string; } interface Init { count: number; } ",
            "declare var BuildValue: { prototype: BuildResult; new(value: string, init: Init): BuildResult; };",
        ));
        let source = parse_source_file("const value = new BuildValue('ready', { count: 1 });");
        let library_file = FileId::new(202_810);
        let file = FileId::new(202_811);
        let mut context = global_object_constructor_context(&library, &source, library_file, file);
        let library_bound = context.file(library_file).unwrap().1.clone();
        let source_bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let (node, _) = variable_new(&source, file, "value");
        let mut plan = plan_direct_default_new_with_source_context(
            &source.arena,
            &source_bound,
            context.store(),
            &host,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            node,
            false,
            &globals,
            options,
        )
        .unwrap();
        let [text, object] = plan.expression_argument_nodes().unwrap() else {
            panic!("two actual arguments")
        };
        let (text, object) = (*text, *object);
        let NodeData::StringLiteral(text_data) = &source.arena.get(text.node).unwrap().data else {
            panic!("the original string argument")
        };
        let NodeData::ObjectLiteralExpression(object_data) =
            &source.arena.get(object.node).unwrap().data
        else {
            panic!("the original object argument")
        };
        let [property] = object_data.properties.nodes.as_slice() else {
            panic!("one real property")
        };
        let NodeData::PropertyAssignment(property) = &source.arena.get(*property).unwrap().data
        else {
            panic!("one assignment")
        };
        let value = NodeRef::new(source.arena.id(), file, property.initializer);
        let NodeData::NumericLiteral(number) = &source.arena.get(value.node).unwrap().data else {
            panic!("the actual numeric value")
        };
        let object_plan = plan_object_literal(context.store(), &host, object).unwrap();
        plan.set_expression_arguments(vec![
            PlannedExpression::new(text, PlannedExpressionKind::String(text_data.text.clone())),
            PlannedExpression::new(
                object,
                PlannedExpressionKind::Object {
                    plan: object_plan,
                    properties: vec![PlannedObjectMember::Eager(PlannedExpression::new(
                        value,
                        PlannedExpressionKind::Number {
                            value: ts_jsnum::from_string(&number.text),
                            unary_operand: None,
                        },
                    ))],
                },
            ),
        ])
        .unwrap();
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        let store = context.store_mut_for_test();
        assert!(store.set_type_node_links(
            value,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            }
        ));
        let before = format!("{store:?}");
        let mut caller = InstantiationSession::new(Default::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        for _ in 0..2 {
            assert_eq!(
                prepare_direct_default_news(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut caller,
                    &mut diagnostics,
                    std::slice::from_ref(&plan),
                ),
                Err(invariant(SourceNewInvariant::InvalidExpressionCache(value)))
            );
            assert_eq!(format!("{store:?}"), before);
            assert!(
                store
                    .value_symbol_links(plan.resolved_symbol())
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            assert!(store.signature_links(node).is_none());
            assert!(store.type_node_links(node).is_none());
            assert_eq!(
                (
                    caller.query_count(),
                    caller.total_count(),
                    caller.limit_event_count()
                ),
                (0, 0, 0)
            );
        }
        assert!(store.set_type_node_links(value, TypeNodeLinks::default()));
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let correct = context.store().type_node_links(value).unwrap().clone();
        let original_pair = (
            context.store().type_node_links(node).cloned(),
            context.store().signature_links(node).cloned(),
        );
        assert!(context.store_mut_for_test().set_type_node_links(
            value,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            }
        ));
        let before = format!("{:?}", context.store());
        assert_eq!(
            preflight_direct_default_new_with_source_context(
                context.store(),
                &host,
                &globals,
                options,
                &plan
            ),
            Err(invariant(SourceNewInvariant::InvalidExpressionCache(value)))
        );
        assert_eq!(format!("{:?}", context.store()), before);
        assert_eq!(
            (
                context.store().type_node_links(node).cloned(),
                context.store().signature_links(node).cloned()
            ),
            original_pair
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(value, correct)
        );
        preflight_direct_default_new_with_source_context(
            context.store(),
            &host,
            &globals,
            options,
            &plan,
        )
        .unwrap();
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_node_links(node).cloned(),
                context.store().signature_links(node).cloned()
            ),
            original_pair
        );
    }

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/class-default-new-poison.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn javascript_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/class-default-new.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn exported_class_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/exported-construction.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn class_symbol(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let name = class.name.and_then(|name| parsed.arena.get(name))?;
                let NodeData::Identifier(name) = &name.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap_or_else(|| panic!("missing class {expected}"));
        let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
        context.store().get_merged_symbol(raw).unwrap()
    }

    fn variable_new(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef) {
        let construction = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.initializer?,
                ))
            })
            .unwrap_or_else(|| panic!("missing variable {expected}"));
        let NodeData::NewExpression(new_expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            panic!("variable initializer is not a new expression")
        };
        (
            construction,
            NodeRef::new(
                construction.arena,
                construction.file,
                new_expression.expression,
            ),
        )
    }

    fn constructor_argument(parsed: &ParseResult, construction: NodeRef) -> NodeRef {
        let NodeData::NewExpression(new_expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            panic!("variable initializer is not a new expression")
        };
        NodeRef::new(
            construction.arena,
            construction.file,
            new_expression.arguments.as_ref().unwrap().nodes[0],
        )
    }

    fn ambient_constructor(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> (NodeRef, SemanticSymbolId) {
        let (declaration, annotation) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, variable.type_?),
                ))
            })
            .unwrap_or_else(|| panic!("missing ambient constructor {expected}"));
        let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
        (annotation, context.store().get_merged_symbol(raw).unwrap())
    }

    fn global_object_constructor_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        library_file: FileId,
        source_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (parsed, file, declaration) in
            [(library, library_file, true), (source, source_file, false)]
        {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(if declaration {
                            "\"/lib/object.d.ts\""
                        } else {
                            "\"/project/object.ts\""
                        }),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(library_file, &library.arena), (source_file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn global_promise_constructor_context<'arena>(
        base: &'arena ParseResult,
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        base_file: FileId,
        library_file: FileId,
        source_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (base, base_file, "\"/lib/es5.d.ts\""),
            (library, library_file, "\"/lib/es2015.promise.d.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        true,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                source_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/promise.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&source.arena, source_file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (base_file, &base.arena),
                (library_file, &library.arena),
                (source_file, &source.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn global_array_constructor_library() -> ParseResult {
        parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface ArrayConstructor { ",
            "new(arrayLength?: number): any[]; ",
            "new<T>(arrayLength: number): T[]; ",
            "new<T>(...items: T[]): T[]; ",
            "(arrayLength?: number): any[]; ",
            "<T>(arrayLength: number): T[]; ",
            "<T>(...items: T[]): T[]; ",
            "readonly prototype: any[]; ",
            "} ",
            "declare var Array: ArrayConstructor;",
        ))
    }

    fn global_boolean_constructor_library() -> ParseResult {
        parse_source_file(concat!(
            "interface Boolean { valueOf(): boolean; } ",
            "interface BooleanConstructor { ",
            "new(value?: any): Boolean; ",
            "<Value>(value?: Value): boolean; ",
            "readonly prototype: Boolean; ",
            "} ",
            "declare var Boolean: BooleanConstructor;",
        ))
    }

    fn global_array_map_constructor_library() -> ParseResult {
        parse_source_file(concat!(
            "interface Array<T> { ",
            "map<U>(callbackfn: ",
            "(value: T, index: number, array: T[]) => U, thisArg?: any): U[]; ",
            "} interface ReadonlyArray<T> {}",
        ))
    }

    fn global_date_constructor_library() -> ParseResult {
        parse_source_file(concat!(
            "interface Date {} ",
            "interface DateConstructor { ",
            "new(): Date; ",
            "new(value: number | string): Date; ",
            "readonly prototype: Date; ",
            "} ",
            "declare var Date: DateConstructor;",
        ))
    }

    fn global_promise_base_library() -> ParseResult {
        parse_source_file("interface PromiseLike<T> {} interface Promise<T> {}")
    }

    fn global_promise_constructor_library() -> ParseResult {
        parse_source_file(concat!(
            "interface PromiseConstructor { ",
            "readonly prototype: Promise<any>; ",
            "new<T>(executor: ",
            "(resolve: (value: T | PromiseLike<T>) => void, ",
            "reject: (reason?: any) => void) => void): Promise<T>; ",
            "} ",
            "declare var Promise: PromiseConstructor;",
        ))
    }

    fn published_global_object_constructor<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        library_file: FileId,
        source_file: FileId,
    ) -> (
        CanonicalCheckerContext<'arena>,
        SemanticSymbolId,
        SemanticSymbolId,
        TypeId,
        TypeId,
        SignatureId,
    ) {
        let mut context =
            global_object_constructor_context(library, source, library_file, source_file);
        let (object, owner, declaration, parameter, annotation, object_type, any) = {
            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let globals = store.symbol_table(bootstrap.globals).unwrap();
            let object = globals
                .get_source("Object")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("ObjectConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let signature_symbol = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                .unwrap();
            let declaration = store
                .symbol(signature_symbol)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let NodeData::ConstructSignatureDeclaration(signature) =
                &library.arena.get(declaration.node).unwrap().data
            else {
                panic!("ObjectConstructor must own its real construct declaration")
            };
            let parameter_node = NodeRef::new(
                declaration.arena,
                declaration.file,
                signature.parameters.nodes[0],
            );
            let parameter = context
                .file(library_file)
                .unwrap()
                .1
                .symbol(parameter_node)
                .unwrap();
            let variable = store.symbol(object).unwrap().value_declaration().unwrap();
            let NodeData::VariableDeclaration(variable) =
                &library.arena.get(variable.node).unwrap().data
            else {
                panic!("Object must retain its library value declaration")
            };
            let annotation =
                NodeRef::new(library.arena.id(), library_file, variable.type_.unwrap());
            let object_type = store
                .declared_type_links(object)
                .and_then(|links| links.declared_type)
                .unwrap();
            (
                object,
                owner,
                declaration,
                parameter,
                annotation,
                object_type,
                bootstrap.any_type,
            )
        };
        let store = context.store_mut_for_test();
        let value_type = if let Some(existing) = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
        {
            existing
        } else {
            let type_ = store
                .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
                .unwrap();
            assert!(store.set_declared_type_links(
                owner,
                DeclaredTypeLinks {
                    declared_type: Some(type_),
                    ..DeclaredTypeLinks::default()
                },
            ));
            type_
        };
        assert!(store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            object,
            ValueSymbolLinks {
                resolved_type: Some(value_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(any),
                ..ValueSymbolLinks::default()
            },
        ));
        let signature = store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                Some(declaration),
                Vec::new(),
                None,
                vec![parameter],
                Some(object_type),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            value_type,
            None,
            None,
            None,
            Some(vec![signature]),
            None,
        ));
        (context, object, owner, value_type, object_type, signature)
    }

    #[test]
    fn exported_class_new_plans_revalidate_the_actual_local_edge_without_publication() {
        enum Family {
            Class,
            Source,
            Overloads,
        }
        for (source, family) in [
            (
                "export class Model { value!: string; } export class Other {} const model = new Model();",
                Family::Class,
            ),
            (
                "export class Model { read() { return 1; } } export class Other {} const model = new Model();",
                Family::Source,
            ),
            (
                "export class Model { constructor(); constructor(value: string); constructor(value?: string) {} } export class Other {} const model = new Model();",
                Family::Overloads,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(202_422);
            let mut context = exported_class_context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let other = class_symbol(&parsed, file, &context, "Other");
            let declaration = context
                .store()
                .symbol(owner)
                .unwrap()
                .value_declaration()
                .unwrap();
            let bound = context.file(file).unwrap().1.clone();
            let local = bound.local_symbol(declaration).unwrap();
            let local_record = context.store().symbol(local).unwrap().clone();
            assert_ne!(local, owner);
            assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
            assert_eq!(local_record.export_symbol(), Some(owner));
            let (construction, constructor) = variable_new(&parsed, file, "model");
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let cold = format!("{:?}", context.store());
            let mut classes = HashMap::new();
            let mut source_classes = HashMap::new();
            match family {
                Family::Class => {
                    classes.insert(
                        owner,
                        super::super::classes::plan_nongeneric_class_members(
                            context.store(),
                            &host,
                            owner,
                        )
                        .unwrap(),
                    );
                }
                Family::Source => {
                    source_classes.insert(
                        owner,
                        super::super::classes::plan_source_class_members(
                            context.store(),
                            &host,
                            owner,
                        )
                        .unwrap(),
                    );
                }
                Family::Overloads => {}
            }
            let plan = plan_direct_default_new(
                &parsed.arena,
                &bound,
                context.store(),
                &host,
                &classes,
                &source_classes,
                &HashMap::new(),
                construction,
                false,
            )
            .unwrap();
            assert!(match family {
                Family::Class => matches!(plan.target, SourceNewTarget::Class(_)),
                Family::Source => matches!(plan.target, SourceNewTarget::SourceClass(_)),
                Family::Overloads =>
                    matches!(plan.target, SourceNewTarget::ConstructorOverloads(_)),
            });
            assert_eq!(plan.resolved_symbol(), local);
            assert_eq!(plan.provider_symbol(), owner);
            assert_eq!(format!("{:?}", context.store()), cold);
            assert!(context.store().symbol_node_links(constructor).is_none());
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().signature_links(construction).is_none());

            assert!(context.store_mut_for_test().set_symbol_relationships(
                local,
                local_record.members(),
                local_record.exports(),
                local_record.parent(),
                Some(other),
            ));
            let damaged = format!("{:?}", context.store());
            for _ in 0..2 {
                assert_eq!(
                    preflight_default_new_cache(context.store(), &host, &plan),
                    Err(invariant(SourceNewInvariant::InvalidClassPlan(declaration))),
                );
                assert_eq!(format!("{:?}", context.store()), damaged);
            }
            assert!(context.store_mut_for_test().set_symbol_relationships(
                local,
                local_record.members(),
                local_record.exports(),
                local_record.parent(),
                local_record.export_symbol(),
            ));
            let restored = format!("{:?}", context.store());
            assert_eq!(
                preflight_default_new_cache(context.store(), &host, &plan),
                Ok(())
            );
            assert_eq!(format!("{:?}", context.store()), restored);
            assert!(context.diagnostics().is_empty());
        }

        let parsed = parse_source_file(
            "export class Model<T> { value!: string; } const model = new Model();",
        );
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(202_423);
        let context = exported_class_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");
        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let (construction, constructor) = variable_new(&parsed, file, "model");
        let cold = format!("{:?}", context.store());
        let class =
            super::super::classes::plan_nongeneric_class_members(context.store(), &host, owner)
                .unwrap();
        assert_eq!(
            plan_direct_default_new(
                &parsed.arena,
                bound,
                context.store(),
                &host,
                &HashMap::from([(owner, class)]),
                &HashMap::new(),
                &HashMap::new(),
                construction,
                false,
            )
            .unwrap_err(),
            unsupported(SourceNewUnsupported::Constructor(constructor)),
        );
        assert_eq!(format!("{:?}", context.store()), cold);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn exported_class_new_keeps_lexical_links_and_rejects_a_class_symbol_in_the_cache() {
        let parsed = parse_source_file(
            "export class Model { read() { return 1; } } const model = new Model();",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_424);
        let mut context = exported_class_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");
        let declaration = context
            .store()
            .symbol(owner)
            .unwrap()
            .value_declaration()
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let local = bound.local_symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let (construction, constructor) = variable_new(&parsed, file, "model");
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let members = completed_source_class_members(context.store(), &host, owner)
            .unwrap()
            .unwrap();
        let value = members.shells().value_type();
        let instance = members.shells().instance_type();
        let signature = members.default_construct_signature();
        assert!(authenticated_class_constructor_value(context.store(), owner).is_none());
        assert_eq!(
            context.store().type_payload(value).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            context
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type,
            Some(instance)
        );
        assert_ne!(local, owner);
        assert_eq!(
            context.store().symbol_node_links(constructor),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(local)
            })
        );
        assert_eq!(
            context
                .store()
                .type_node_links(constructor)
                .unwrap()
                .resolved_type,
            Some(value)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(construction)
                .unwrap()
                .resolved_type,
            Some(instance)
        );
        assert_eq!(
            context
                .store()
                .signature_links(construction)
                .unwrap()
                .resolved_signature,
            ResolvedSignatureState::Resolved(signature)
        );
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(instance)
        );
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
                context.store().type_node_links(constructor).cloned(),
                context.store().type_node_links(construction).cloned(),
                context.store().signature_links(construction).cloned(),
            )
        };
        let warm = snapshot(&context);
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), warm);
        assert!(context.store_mut_for_test().set_symbol_node_links(
            constructor,
            SymbolNodeLinks {
                resolved_symbol: Some(owner)
            }
        ));
        let damaged = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(
                context.recheck_source_file(file),
                Err(SourceCheckError::Call(constructor))
            );
            assert_eq!(snapshot(&context), damaged);
            assert_eq!(
                context.store().symbol_node_links(constructor),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(owner)
                })
            );
        }
        assert!(context.store_mut_for_test().set_symbol_node_links(
            constructor,
            SymbolNodeLinks {
                resolved_symbol: Some(local)
            }
        ));
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), warm);
        let restored = completed_source_class_members(context.store(), &host, owner)
            .unwrap()
            .unwrap();
        assert_eq!(
            (
                restored.shells().value_type(),
                restored.shells().instance_type(),
                restored.default_construct_signature()
            ),
            (value, instance, signature),
        );
    }

    fn generic_new_plan_for_test(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
        owner: SemanticSymbolId,
        construction: NodeRef,
    ) -> SourceDefaultNewPlan {
        let host = context.declared_type_host().unwrap();
        let (_, bound) = context.file(file).unwrap();
        let type_context = ClassTypeQueryContext::new(context.global_types(), context.options());
        let class = super::super::classes::plan_source_class_members_with_type_context(
            context.store(),
            &host,
            owner,
            Some(&type_context),
        )
        .unwrap();
        plan_direct_default_new_with_type_context(
            &parsed.arena,
            bound,
            context.store(),
            &host,
            &HashMap::new(),
            &HashMap::from([(owner, class)]),
            &HashMap::new(),
            construction,
            false,
            Some(&type_context),
        )
        .unwrap()
    }

    #[test]
    fn generic_source_new_keeps_late_publication_and_the_spent_caller() {
        use crate::semantic::classes::{
            finish_source_class_members, plan_source_class_members_with_type_context,
            prepare_source_class_members_with_type_queries,
        };
        use crate::semantic::instantiate::{InstantiationLimits, instantiate_type_with_session};

        let parsed =
            parse_source_file("export class Defaults<T = string> {} const item = new Defaults();");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(204_210);
        let mut context = exported_class_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Defaults");
        let (construction, constructor) = variable_new(&parsed, file, "item");
        let bound = context.file(file).unwrap().1.clone();
        let options = context.options();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let type_context = ClassTypeQueryContext::new(&globals, options);
        let class = plan_source_class_members_with_type_context(
            context.store(),
            &host,
            owner,
            Some(&type_context),
        )
        .unwrap();
        assert!(class.bodies().is_empty());
        let mut setup_session = InstantiationSession::new(InstantiationLimits::default());
        let mut setup_diagnostics = CanonicalCheckerDiagnostics::default();
        let prepared_class = prepare_source_class_members_with_type_queries(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut setup_session,
            &mut setup_diagnostics,
            &class,
        )
        .unwrap();
        let members = finish_source_class_members(
            context.store_mut_for_test(),
            &host,
            &class,
            &prepared_class,
        )
        .unwrap();
        assert!(setup_diagnostics.is_empty());
        let mut plan = generic_new_plan_for_test(&context, &parsed, file, owner, construction);
        assert!(plan.is_generic_source_class());
        plan.set_expression_arguments(Vec::new()).unwrap();
        prepare_direct_default_news(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut setup_session,
            &mut setup_diagnostics,
            std::slice::from_ref(&plan),
        )
        .unwrap();
        let prepared = check_source_generic_class_new(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut setup_session,
            &plan,
            None,
            &[],
            None,
        )
        .unwrap();
        let checked = prepared.checked;
        assert!(prepared.access_diagnostic().is_none());
        assert!(prepared.resolution().unwrap().diagnostic.is_none());
        assert_eq!(
            exact_signature_cache(context.store(), construction),
            Ok(None)
        );
        assert_eq!(exact_type_cache(context.store(), construction), Ok(None));
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let reference =
            validate_direct_generic_reference(context.store(), checked.instance_type).unwrap();
        assert_eq!(reference.target, members.shells().instance_type());
        assert_eq!(reference.type_arguments, [string]);
        let original = members.default_construct_signature();
        let original_record = context.store().signature(original).unwrap();
        let [formal] = original_record.type_parameters() else {
            panic!("the real default constructor must retain its one class formal")
        };
        let formal = *formal;
        let mapper = context
            .store()
            .signature(checked.signature)
            .unwrap()
            .mapper()
            .unwrap();
        assert_eq!(
            context
                .store()
                .signature(checked.signature)
                .unwrap()
                .target(),
            Some(original)
        );
        let old_symbol = context
            .store()
            .symbol_node_links(constructor)
            .unwrap()
            .clone();
        assert!(context.store_mut_for_test().set_symbol_node_links(
            constructor,
            SymbolNodeLinks {
                resolved_symbol: Some(owner)
            },
        ));
        let damaged = format!("{:?}", context.store());
        assert_eq!(
            publish_source_generic_class_new(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut setup_session,
                &plan,
                None,
                &[],
                None,
                prepared,
            ),
            Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                constructor
            )))
        );
        assert_eq!(format!("{:?}", context.store()), damaged);
        assert_eq!(
            exact_signature_cache(context.store(), construction),
            Ok(None)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_node_links(constructor, old_symbol)
        );

        let mut caller = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        assert_eq!(
            instantiate_type_with_session(
                context.store_mut_for_test(),
                formal,
                mapper,
                Some(CanonicalArrayTargets::from_global_types(&globals)),
                &mut caller,
            ),
            Ok(string)
        );
        let spent = (caller.query_count(), caller.total_count());
        assert_eq!(spent, (1, 1));
        let limit_mark = caller.limit_event_mark();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        let prepared = check_source_generic_class_new(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut caller,
            &plan,
            None,
            &[],
            None,
        )
        .unwrap();
        assert_eq!(prepared.checked, checked);
        assert_eq!(
            exact_signature_cache(context.store(), construction),
            Ok(None)
        );
        assert_eq!(
            publish_source_generic_class_new(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut caller,
                &plan,
                None,
                &[],
                None,
                prepared,
            ),
            Ok(checked)
        );
        assert_eq!((caller.query_count(), caller.total_count()), spent);
        assert!(!caller.limit_event_occurred_since(limit_mark));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert_eq!(
            exact_signature_cache(context.store(), construction),
            Ok(Some(checked.signature))
        );
        assert_eq!(
            exact_type_cache(context.store(), construction),
            Ok(Some(checked.instance_type))
        );
        context.check_source_file(file).unwrap();
        let warm = format!("{:?}", context.store());
        context.recheck_source_file(file).unwrap();
        assert_eq!(format!("{:?}", context.store()), warm);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn generic_source_new_rejects_changed_cached_requests_and_returns() {
        use crate::semantic::instantiate::InstantiationLimits;

        let parsed = parse_source_file(concat!(
            "export class Box<T> {} ",
            "const text = new Box<string>(); const count = new Box<number>();",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(204_211);
        let mut context = exported_class_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Box");
        let (text, _) = variable_new(&parsed, file, "text");
        let (count, _) = variable_new(&parsed, file, "count");
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let text_signature = exact_signature_cache(context.store(), text)
            .unwrap()
            .unwrap();
        let count_signature = exact_signature_cache(context.store(), count)
            .unwrap()
            .unwrap();
        let text_result = exact_type_cache(context.store(), text).unwrap().unwrap();
        let count_result = exact_type_cache(context.store(), count).unwrap().unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let bound = context.file(file).unwrap().1.clone();
        let options = context.options();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut plan = generic_new_plan_for_test(&context, &parsed, file, owner, text);
        plan.set_expression_arguments(Vec::new()).unwrap();
        let [written] = plan.written_type_argument_nodes().unwrap() else {
            panic!("the first New must retain its real written string argument")
        };
        let written = *written;
        assert_eq!(host.node(written).unwrap().kind, SyntaxKind::StringKeyword);
        assert_eq!(exact_type_cache(context.store(), written), Ok(Some(string)));
        let (original_target, original_mapper) = {
            let signature = context.store().signature(text_signature).unwrap();
            (signature.target(), signature.mapper())
        };
        let count_mapper = context
            .store()
            .signature(count_signature)
            .unwrap()
            .mapper()
            .unwrap();
        assert_ne!(original_mapper, Some(count_mapper));
        assert_eq!(
            original_target,
            context.store().signature(count_signature).unwrap().target()
        );
        assert!(
            context
                .store_mut_for_test()
                .set_signature_target_and_mapper(
                    text_signature,
                    original_target,
                    Some(count_mapper),
                )
        );
        let damaged = format!("{:?}", context.store());
        for _ in 0..2 {
            assert_eq!(
                preflight_source_generic_class_new_with_context(
                    context.store(),
                    &host,
                    &globals,
                    options,
                    &plan,
                    None,
                ),
                Err(invariant(SourceNewInvariant::InvalidExpressionCache(text)))
            );
            assert_eq!(format!("{:?}", context.store()), damaged);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_signature_target_and_mapper(text_signature, original_target, original_mapper,)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(text_signature, Some(number),)
        );
        let damaged = format!("{:?}", context.store());
        assert_eq!(
            preflight_source_generic_class_new_with_context(
                context.store(),
                &host,
                &globals,
                options,
                &plan,
                None,
            ),
            Err(invariant(SourceNewInvariant::InvalidExpressionCache(text)))
        );
        assert_eq!(format!("{:?}", context.store()), damaged);
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(text_signature, Some(text_result),)
        );

        let saved_signature = context.store().signature_links(text).unwrap().clone();
        let saved_type = context.store().type_node_links(text).unwrap().clone();
        assert!(context.store_mut_for_test().set_signature_links(
            text,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(count_signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(context.store_mut_for_test().set_type_node_links(
            text,
            TypeNodeLinks {
                resolved_type: Some(count_result),
                ..TypeNodeLinks::default()
            },
        ));
        let damaged = format!("{:?}", context.store());
        let mut caller = InstantiationSession::new(InstantiationLimits::default());
        for _ in 0..2 {
            let error = check_source_generic_class_new(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut caller,
                &plan,
                None,
                &[],
                Some(&[string]),
            )
            .err()
            .unwrap();
            assert_eq!(
                error,
                invariant(SourceNewInvariant::InvalidExpressionCache(text))
            );
            assert_eq!(format!("{:?}", context.store()), damaged);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(text, saved_signature)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(text, saved_type)
        );

        let saved_written = context.store().type_node_links(written).unwrap().clone();
        assert!(context.store_mut_for_test().set_type_node_links(
            written,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        let damaged = format!("{:?}", context.store());
        for _ in 0..2 {
            assert_eq!(
                preflight_generic_new_arguments(context.store(), &plan, &[], Some(&[string])),
                Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    written
                )))
            );
            assert_eq!(format!("{:?}", context.store()), damaged);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(written, saved_written)
        );
        context.recheck_source_file(file).unwrap();
        let warm = format!("{:?}", context.store());
        context.recheck_source_file(file).unwrap();
        assert_eq!(format!("{:?}", context.store()), warm);
        assert_eq!(
            exact_signature_cache(context.store(), text),
            Ok(Some(text_signature))
        );
        assert_eq!(
            exact_type_cache(context.store(), text),
            Ok(Some(text_result))
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn generic_source_new_access_errors_keep_the_real_error_signature() {
        let parsed = parse_source_file(concat!(
            "class Secret<T> { private constructor(value: T) {} } ",
            "abstract class Abstract<T> {} ",
            "const secret = new Secret<string>('kept'); ",
            "const abstractValue = new Abstract<number>();",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(204_212);
        let mut context = context(&parsed, file);
        let secret = class_symbol(&parsed, file, &context, "Secret");
        let abstract_owner = class_symbol(&parsed, file, &context, "Abstract");
        let (secret_new, _) = variable_new(&parsed, file, "secret");
        let (abstract_new, _) = variable_new(&parsed, file, "abstractValue");
        let unknown_signature = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature;
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        context.check_source_file(file).unwrap();
        let diagnostics = context.diagnostics().clone();
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2673, 2511]
        );
        assert_eq!(diagnostics.as_slice()[0].node, Some(secret_new));
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.arguments,
            ["Secret<T>".to_owned()]
        );
        assert_eq!(diagnostics.as_slice()[1].node, Some(abstract_new));
        assert!(diagnostics.as_slice()[1].diagnostic.arguments.is_empty());
        for (owner, new) in [(secret, secret_new), (abstract_owner, abstract_new)] {
            assert_eq!(
                exact_signature_cache(context.store(), new),
                Ok(Some(unknown_signature))
            );
            assert_eq!(exact_type_cache(context.store(), new), Ok(Some(error_type)));
            let host = context.declared_type_host().unwrap();
            let constructors = super::super::classes::completed_source_class_constructors(
                context.store(),
                &host,
                owner,
            )
            .unwrap()
            .unwrap();
            let origin = constructors.members().shells().instance_type();
            let TypeData::Interface(interface) =
                context.store().type_payload(origin).unwrap().data()
            else {
                panic!("the error must preserve its real class origin")
            };
            let TypeCacheState::Allocated(instantiations) =
                &interface.reference.object.instantiations
            else {
                panic!("the class origin must retain its canonical self cache")
            };
            let formals = interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap();
            assert_eq!(instantiations.len(), 1);
            assert_eq!(instantiations.get(&type_list_key(formals)), Some(&origin));
            let explicit = if owner == secret {
                context.store().intrinsic_bootstrap().unwrap().string_type
            } else {
                context.store().intrinsic_bootstrap().unwrap().number_type
            };
            for callable in constructors.signatures() {
                assert_eq!(
                    context.store().cached_signature(
                        callable.signature,
                        type_list_key(&[explicit]),
                        &[explicit]
                    ),
                    CachedSignatureLookup::Missing
                );
            }
        }
        assert_eq!(
            context.get_return_type_of_signature(unknown_signature),
            Ok(error_type)
        );
        let bound = context.file(file).unwrap().1.clone();
        let options = context.options();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let plan = generic_new_plan_for_test(&context, &parsed, file, secret, secret_new);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(unknown_signature, Some(number))
        );
        let damaged = format!("{:?}", context.store());
        for _ in 0..2 {
            assert_eq!(
                generic_new_error_signature_return_type(context.store(), unknown_signature),
                Err(invariant(SourceNewInvariant::InvalidConstructSignature(
                    unknown_signature
                )))
            );
            assert_eq!(
                preflight_source_generic_class_new_with_context(
                    context.store(),
                    &host,
                    &globals,
                    options,
                    &plan,
                    None,
                ),
                Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                    secret_new
                )))
            );
            assert_eq!(format!("{:?}", context.store()), damaged);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(unknown_signature, Some(error_type))
        );
        context.recheck_source_file(file).unwrap();
        let warm = format!("{:?}", context.store());
        context.recheck_source_file(file).unwrap();
        assert_eq!(format!("{:?}", context.store()), warm);
        assert_eq!(context.diagnostics(), &diagnostics);

        let method_parsed = parse_source_file(concat!(
            "class Secret<T> { private constructor(value: T) {} } ",
            "class Caller { make(): unknown { return new Secret<number>(1); } }",
        ));
        assert!(method_parsed.diagnostics.is_empty());
        let method_file = FileId::new(204_213);
        let mut method_context = self::context(&method_parsed, method_file);
        let method_new = method_parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    method_parsed.arena.id(),
                    method_file,
                    node,
                ))
            })
            .unwrap();
        method_context.check_source_file(method_file).unwrap();
        let method_diagnostics = method_context.diagnostics().clone();
        let [diagnostic] = method_diagnostics.as_slice() else {
            panic!("the real private access must report one constructor diagnostic")
        };
        assert_eq!(diagnostic.node, Some(method_new));
        assert_eq!(diagnostic.diagnostic.code(), 2673);
        assert_eq!(diagnostic.diagnostic.arguments, ["Secret<T>".to_owned()]);
        let bootstrap = method_context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            exact_signature_cache(method_context.store(), method_new),
            Ok(Some(bootstrap.unknown_signature))
        );
        assert_eq!(
            exact_type_cache(method_context.store(), method_new),
            Ok(Some(bootstrap.error_type))
        );
        let method_warm = format!("{:?}", method_context.store());
        for _ in 0..2 {
            method_context.recheck_source_file(method_file).unwrap();
            assert_eq!(format!("{:?}", method_context.store()), method_warm);
            assert_eq!(method_context.diagnostics(), &method_diagnostics);
        }
    }

    #[test]
    fn source_class_default_new_reuses_completed_caches_and_rejects_foreign_signatures() {
        let parsed = parse_source_file(concat!(
            "class Model { read() { return 1; } } ",
            "class Other { read() { return 2; } } ",
            "const model = new Model();",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_420);
        let mut context = context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");
        let other = class_symbol(&parsed, file, &context, "Other");
        let (construction, constructor) = variable_new(&parsed, file, "model");
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let (value, signature) =
            authenticated_class_constructor_value(context.store(), owner).unwrap();
        let instance = context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(constructor)
                .unwrap()
                .resolved_type,
            Some(value)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(construction)
                .unwrap()
                .resolved_type,
            Some(instance)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor)
                .unwrap()
                .resolved_symbol,
            Some(owner)
        );
        assert_eq!(
            context
                .store()
                .signature_links(construction)
                .unwrap()
                .resolved_signature,
            ResolvedSignatureState::Resolved(signature),
        );
        let selected = context.store().signature(signature).unwrap();
        assert_eq!(selected.flags(), SignatureFlags::CONSTRUCT);
        assert!(selected.declaration().is_none());
        assert!(selected.parameters().is_empty());
        assert!(selected.type_parameters().is_empty());
        assert_eq!(selected.min_argument_count(), 0);
        assert_eq!(selected.resolved_return_type(), Some(instance));
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            )
        };
        let warm = snapshot(&context);
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), warm);
        assert_eq!(
            authenticated_class_constructor_value(context.store(), owner),
            Some((value, signature))
        );
        let (_, foreign) = authenticated_class_constructor_value(context.store(), other).unwrap();
        assert_ne!(foreign, signature);
        assert!(context.store_mut_for_test().set_signature_links(
            construction,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(foreign),
                ..SignatureLinks::default()
            },
        ));
        let poisoned = snapshot(&context);
        assert_eq!(
            context.recheck_source_file(file),
            Err(SourceCheckError::Call(construction))
        );
        assert_eq!(snapshot(&context), poisoned);
        assert_eq!(
            authenticated_class_constructor_value(context.store(), owner),
            Some((value, signature))
        );
    }

    #[test]
    fn source_class_default_new_keeps_abstract_and_explicit_constructor_boundaries() {
        let parsed = parse_source_file(concat!(
            "abstract class Model { read() { return 1; } } ",
            "const model = new Model();",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(202_421);
        let mut abstract_context = context(&parsed, file);
        let (construction, _) = variable_new(&parsed, file, "model");
        abstract_context.check_source_file(file).unwrap();
        let [diagnostic] = abstract_context.diagnostics().as_slice() else {
            panic!("abstract construction must retain its one diagnostic");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2511);
        assert_eq!(diagnostic.node, Some(construction));
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Cannot create an instance of an abstract class."
        );
        let diagnostics = abstract_context.diagnostics().clone();
        abstract_context.recheck_source_file(file).unwrap();
        assert_eq!(abstract_context.diagnostics(), &diagnostics);

        for (source, explicit_constructor) in [
            (
                "class Model { private constructor() {} read() { return 1; } } const model = new Model();",
                true,
            ),
            (
                "class Model { read() { return 1; } } const model = new Model(1);",
                false,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, constructor) = variable_new(&parsed, file, "model");
            let rejected = if explicit_constructor {
                constructor
            } else {
                construction
            };
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                    rejected
                ))),
                "{source}",
            );
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.store().signature_links(construction).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn global_object_constructor_materializes_real_signature_and_keeps_other_members_lazy() {
        let library = parse_source_file(concat!(
            "interface Object {} ",
            "interface ObjectConstructor { ",
            "new(value?: any): Object; ",
            "readonly prototype: Object; ",
            "} ",
            "declare var Object: ObjectConstructor;",
        ));
        let source = parse_source_file("const result = new Object();");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_813);
        let source_file = FileId::new(1_814);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (object, owner, declaration, object_type, initial_symbols) = {
            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let globals = store.symbol_table(bootstrap.globals).unwrap();
            let object = globals
                .get_source("Object")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("ObjectConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let declaration = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                .and_then(|signature| store.symbol(signature))
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first())
                .copied()
                .unwrap();
            let object_type = store
                .declared_type_links(object)
                .and_then(|links| links.declared_type)
                .unwrap();
            assert!(store.declared_type_links(owner).is_none());
            assert!(store.signature_links(declaration).is_none());
            (object, owner, declaration, object_type, store.symbol_len())
        };
        let (construction, constructor) = variable_new(&source, source_file, "result");

        context.check_source_file(source_file).unwrap();

        let store = context.store();
        let value_type = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .unwrap();
        let value_record = store.type_payload(value_type).unwrap();
        let TypeData::Interface(interface) = value_record.data() else {
            panic!("ObjectConstructor must preserve its real interface identity")
        };
        assert!(
            !value_record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(!interface.declared_members_resolved);
        assert!(interface.reference.object.structured.signatures.is_none());
        let signature = store
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let signature_record = store.signature(signature).unwrap();
        assert_eq!(signature_record.declaration(), Some(declaration));
        assert_eq!(signature_record.resolved_return_type(), Some(object_type));
        assert_eq!(signature_record.min_argument_count(), 0);
        assert_eq!(store.symbol_len(), initial_symbols);
        assert_eq!(
            store.symbol_node_links(constructor),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(object),
            }),
        );
        assert_eq!(
            store.signature_links(construction),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            }),
        );
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(object_type)
        );
        let TypeData::Interface(interface) =
            context.store().type_payload(value_type).unwrap().data()
        else {
            panic!("ObjectConstructor must remain an interface after its return query")
        };
        assert!(!interface.declared_members_resolved);
        assert!(interface.reference.object.structured.signatures.is_none());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn global_object_constructor_casts_to_empty_interfaces_without_resolving_object_members() {
        let library = parse_source_file(concat!(
            "interface Object { valueOf(): Object; } ",
            "interface ObjectConstructor { ",
            "new(value?: any): Object; ",
            "readonly prototype: Object; ",
            "} ",
            "declare var Object: ObjectConstructor;",
        ));
        let source = parse_source_file("interface Foo {} const result = <Foo> new Object();");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_823);
        let source_file = FileId::new(1_824);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let object_type = context.global_types().object_type;
        let before_symbols = context.store().symbol_len();

        context.check_source_file(source_file).unwrap();

        assert_eq!(context.store().symbol_len(), before_symbols);
        let object = context.store().type_payload(object_type).unwrap();
        assert!(
            !object
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(context.diagnostics().is_empty());
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn global_object_constructor_reuses_optional_signature_and_replays_warm() {
        let library = parse_source_file(concat!(
            "interface Object {} ",
            "interface ObjectConstructor { new(value?: any): Object; } ",
            "declare var Object: ObjectConstructor;",
        ));
        let source = parse_source_file("const result = new Object();");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_815);
        let source_file = FileId::new(1_816);
        let (mut context, object, _, value_type, object_type, signature) =
            published_global_object_constructor(&library, &source, library_file, source_file);
        let (construction, constructor) = variable_new(&source, source_file, "result");
        let before_signatures = context.store().signature_len();
        let before_symbols = context.store().symbol_len();

        context.check_source_file(source_file).unwrap();

        let store = context.store();
        assert_eq!(store.signature_len(), before_signatures);
        assert_eq!(store.symbol_len(), before_symbols);
        assert_eq!(
            store.symbol_node_links(constructor),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(object),
            }),
        );
        assert_eq!(
            store.type_node_links(constructor),
            Some(&TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            }),
        );
        assert_eq!(
            store.type_node_links(construction),
            Some(&TypeNodeLinks {
                resolved_type: Some(object_type),
                ..TypeNodeLinks::default()
            }),
        );
        assert_eq!(
            store.signature_links(construction),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            }),
        );
        assert_eq!(store.signature(signature).unwrap().min_argument_count(), 0);
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn readonly_date_parameter_defaults_allow_omitted_class_constructor_arguments() {
        let library = global_date_constructor_library();
        let source = parse_source_file(concat!(
            "class Model { constructor(readonly timestamp = new Date()) {} } ",
            "const value = new Model();",
        ));
        let library_file = FileId::new(1_846);
        let source_file = FileId::new(1_847);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (construction, _) = variable_new(&source, source_file, "value");

        context.check_source_file(source_file).unwrap();

        let store = context.store();
        let class = store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Model"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .unwrap();
        let class_type = store
            .declared_type_links(class)
            .and_then(|links| links.declared_type)
            .unwrap();
        let signature = store
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        assert_eq!(store.signature(signature).unwrap().parameters().len(), 1);
        assert_eq!(store.signature(signature).unwrap().min_argument_count(), 0);
        assert_eq!(
            store.type_node_links(construction),
            Some(&TypeNodeLinks {
                resolved_type: Some(class_type),
                ..TypeNodeLinks::default()
            }),
        );
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn global_object_constructor_rejects_forged_signatures_without_expression_publication() {
        for poison in 0..3 {
            let library = parse_source_file(concat!(
                "interface Object {} ",
                "interface ObjectConstructor { new(value?: any): Object; } ",
                "declare var Object: ObjectConstructor;",
            ));
            let source = parse_source_file("const result = new Object();");
            let library_file = FileId::new(1_817 + poison * 2);
            let source_file = FileId::new(1_818 + poison * 2);
            let (mut context, object, owner, _, _, signature) =
                published_global_object_constructor(&library, &source, library_file, source_file);
            let (construction, constructor) = variable_new(&source, source_file, "result");
            match poison {
                0 => {
                    assert!(context.store_mut_for_test().set_signature_flags(
                        signature,
                        SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT,
                    ));
                }
                1 => {
                    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(signature, Some(string))
                    );
                }
                2 => {
                    let globals = context.store().intrinsic_bootstrap().unwrap().globals;
                    assert_eq!(
                        context.store_mut_for_test().insert_symbol(
                            globals,
                            EscapedName::source("Object"),
                            owner,
                        ),
                        Some(Some(object)),
                    );
                }
                _ => unreachable!("global Object poison cases are bounded"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                context.check_source_file(source_file).is_err(),
                "case {poison}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "case {poison}",
            );
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().symbol_node_links(constructor).is_none());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Verify wrapper ownership, both literal forms, and warm identity.
    fn global_boolean_constructor_preserves_optional_signature_and_fresh_literals() {
        let library = global_boolean_constructor_library();
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);

        for (index, (argument, expected_boolean)) in [
            ("", None),
            ("true", Some(true)),
            ("false", Some(false)),
            ("{}", None),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parse_source_file(&format!("const result = new Boolean({argument});"));
            assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
            let library_file = FileId::new(1_850 + u32::try_from(index).unwrap() * 2);
            let source_file = FileId::new(1_851 + u32::try_from(index).unwrap() * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (construction, constructor) = variable_new(&source, source_file, "result");
            let (boolean, owner, call, prototype) = {
                let store = context.store();
                let globals = store
                    .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                    .unwrap();
                let boolean = globals
                    .get_source("Boolean")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let owner = globals
                    .get_source("BooleanConstructor")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let members = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .unwrap();
                (
                    boolean,
                    owner,
                    members.get(InternalSymbolName::Call.as_ref()).unwrap(),
                    members.get_source("prototype").unwrap(),
                )
            };

            context.check_source_file(source_file).unwrap();

            let store = context.store();
            let expected_instance = context.global_types().boolean_type;
            let value = store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let TypeData::Interface(interface) = store.type_payload(value).unwrap().data() else {
                panic!("BooleanConstructor must retain its library interface")
            };
            assert!(!interface.declared_members_resolved);
            assert!(interface.reference.object.structured.signatures.is_none());
            assert!(store.value_symbol_links(prototype).is_none());
            let call_declaration = store.symbol(call).unwrap().declarations().unwrap()[0];
            assert!(store.signature_links(call_declaration).is_none());
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let record = store.signature(signature).unwrap();
            assert_eq!(record.min_argument_count(), 0);
            assert_eq!(record.resolved_return_type(), Some(expected_instance));
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(boolean),
            );
            assert_eq!(
                store
                    .type_node_links(construction)
                    .and_then(|links| links.resolved_type),
                Some(expected_instance),
            );
            if let Some(boolean) = expected_boolean {
                let argument = constructor_argument(&source, construction);
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                assert_eq!(
                    store
                        .type_node_links(argument)
                        .and_then(|links| links.resolved_type),
                    Some(if boolean {
                        bootstrap.true_type
                    } else {
                        bootstrap.false_type
                    }),
                );
            } else if argument == "{}" {
                let object = constructor_argument(&source, construction);
                let object_type = store
                    .type_node_links(object)
                    .and_then(|links| links.resolved_type)
                    .expect("Boolean's object argument must preserve its resolved object type");
                assert!(matches!(
                    store
                        .type_payload(object_type)
                        .map(super::super::type_records::TypeRecord::data),
                    Some(TypeData::Object(_)),
                ));
            }
            assert!(context.diagnostics().is_empty());
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected_instance),
            );
            let TypeData::Interface(interface) =
                context.store().type_payload(value).unwrap().data()
            else {
                panic!("BooleanConstructor must remain an interface after its return query")
            };
            assert!(!interface.declared_members_resolved);
            assert!(interface.reference.object.structured.signatures.is_none());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );

            context.recheck_source_file(source_file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn global_boolean_constructor_and_filter_reuse_the_same_authenticated_signature() {
        let library = parse_source_file(concat!(
            "interface Array<Value> { ",
            "filter<Narrowed extends Value>(predicate: ",
            "(value: Value, index: number, array: Value[]) => value is Narrowed, ",
            "thisArg?: any): Narrowed[]; ",
            "filter(predicate: ",
            "(value: Value, index: number, array: Value[]) => unknown, ",
            "thisArg?: any): Value[]; ",
            "} ",
            "interface ReadonlyArray<Value> {} ",
            "interface Boolean { valueOf(): boolean; } ",
            "interface BooleanConstructor { ",
            "new(value?: any): Boolean; ",
            "<Value>(value?: Value): boolean; ",
            "readonly prototype: Boolean; ",
            "} ",
            "declare var Boolean: BooleanConstructor;",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);

        for (index, source_text) in [
            concat!(
                "declare const values: any[]; ",
                "const wrapped = new Boolean(true); ",
                "const filtered: any[] = values.filter(Boolean);",
            ),
            concat!(
                "declare const values: any[]; ",
                "const filtered: any[] = values.filter(Boolean); ",
                "const wrapped = new Boolean(true);",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parse_source_file(source_text);
            assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
            let library_file = FileId::new(1_860 + u32::try_from(index).unwrap() * 2);
            let source_file = FileId::new(1_861 + u32::try_from(index).unwrap() * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (construction, _) = variable_new(&source, source_file, "wrapped");

            context.check_source_file(source_file).unwrap();

            let store = context.store();
            let globals = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap();
            let owner = globals
                .get_source("BooleanConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner_type = store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let construction_signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let StoredCallableSetValidation::Valid { projection, .. } =
                validate_stored_callable_set(store, owner_type)
            else {
                panic!("BooleanConstructor must publish authenticated call and construct sets")
            };
            assert_eq!(projection.call_signatures.len(), 1);
            assert_eq!(
                projection.construct_signatures.as_ref(),
                &[construction_signature],
            );
            assert_eq!(
                store.declared_call_set_type_for_signature(construction_signature),
                Some(owner_type),
            );
            let expected_instance = context.global_types().boolean_type;
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                context.get_return_type_of_signature(construction_signature),
                Ok(expected_instance),
            );
            assert!(context.diagnostics().is_empty());
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
                "{source_text}",
            );
        }
    }

    #[test]
    fn lazy_boolean_constructor_upgrades_without_replacing_or_trusting_a_poisoned_signature() {
        let library = global_boolean_constructor_library();

        for (index, poison) in [false, true].into_iter().enumerate() {
            let source = parse_source_file("const result = new Boolean(true);");
            let library_file = FileId::new(1_868 + u32::try_from(index).unwrap() * 2);
            let source_file = FileId::new(1_869 + u32::try_from(index).unwrap() * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (construction, _) = variable_new(&source, source_file, "result");

            context.check_source_file(source_file).unwrap();

            let owner = context
                .store()
                .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source("BooleanConstructor"))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let instance = context.global_types().boolean_type;

            if poison {
                let incorrect = context.store().intrinsic_bootstrap().unwrap().string_type;
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(signature, Some(incorrect))
                );
                let poisoned = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                );
                assert!(context.get_declared_type_of_symbol(owner).is_err());
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    poisoned,
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(signature, Some(instance))
                );
            }

            let constructor = context.get_declared_type_of_symbol(owner).unwrap();
            let StoredCallableSetValidation::Valid { projection, .. } =
                validate_stored_callable_set(context.store(), constructor)
            else {
                panic!("BooleanConstructor must publish an authenticated callable set")
            };
            assert_eq!(projection.call_signatures.len(), 1);
            assert_eq!(projection.construct_signatures.as_ref(), &[signature]);
            assert_eq!(
                context
                    .store()
                    .declared_call_set_type_for_signature(signature),
                Some(constructor),
            );
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(instance)
            );
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(constructor));
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn lazy_global_wrapper_constructor_returns_reject_poisoned_signatures() {
        for (index, (name, library_text)) in [
            (
                "Object",
                concat!(
                    "interface Object {} ",
                    "interface ObjectConstructor { ",
                    "new(value?: any): Object; ",
                    "readonly prototype: Object; ",
                    "} declare var Object: ObjectConstructor;",
                ),
            ),
            (
                "Boolean",
                concat!(
                    "interface Boolean { valueOf(): boolean; } ",
                    "interface BooleanConstructor { ",
                    "new(value?: any): Boolean; ",
                    "<Value>(value?: Value): boolean; ",
                    "readonly prototype: Boolean; ",
                    "} declare var Boolean: BooleanConstructor;",
                ),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let library = parse_source_file(library_text);
            let source = parse_source_file(&format!("const result = new {name}();"));
            let library_file = FileId::new(1_864 + u32::try_from(index).unwrap() * 2);
            let source_file = FileId::new(1_865 + u32::try_from(index).unwrap() * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (construction, _) = variable_new(&source, source_file, "result");

            context.check_source_file(source_file).unwrap();

            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let expected = context
                .store()
                .signature(signature)
                .and_then(Signature::resolved_return_type)
                .unwrap();
            let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert!(
                context
                    .store_mut_for_test()
                    .set_signature_resolved_return_type(signature, Some(poison))
            );
            let poisoned = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(matches!(
                context.get_return_type_of_signature(signature),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    super::super::type_nodes::TypeNodeUnavailable::InvalidFunctionSignature(actual)
                )) if actual == signature
            ));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                poisoned,
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_signature_resolved_return_type(signature, Some(expected))
            );
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );

            let globals = context.store().intrinsic_bootstrap().unwrap().globals;
            let instance = context
                .store()
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let owner = context
                .store()
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(&format!("{name}Constructor")))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let value_annotation = context
                .store()
                .symbol(instance)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .and_then(|declaration| context.store().source_direct_type_annotation(declaration))
                .unwrap();
            let return_annotation = context
                .store()
                .function_signature_return_annotation(signature)
                .unwrap()
                .0;
            for (annotation, incorrect) in
                [(value_annotation, instance), (return_annotation, owner)]
            {
                let original = context
                    .store()
                    .symbol_node_links(annotation)
                    .cloned()
                    .unwrap();
                assert!(context.store_mut_for_test().set_symbol_node_links(
                    annotation,
                    SymbolNodeLinks {
                        resolved_symbol: Some(incorrect),
                    },
                ));
                let poisoned = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                );

                assert!(matches!(
                    context.get_return_type_of_signature(signature),
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        super::super::type_nodes::TypeNodeUnavailable::InvalidFunctionSignature(
                            actual,
                        )
                    )) if actual == signature
                ));
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    poisoned,
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_symbol_node_links(annotation, original)
                );
                assert_eq!(
                    context.get_return_type_of_signature(signature),
                    Ok(expected)
                );
            }
        }
    }

    #[test]
    fn global_boolean_constructor_rejects_poisoned_literal_before_publication() {
        let library = global_boolean_constructor_library();
        let source = parse_source_file("const result = new Boolean(true);");
        let library_file = FileId::new(1_856);
        let source_file = FileId::new(1_857);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (construction, constructor) = variable_new(&source, source_file, "result");
        let argument = constructor_argument(&source, construction);
        let owner = context
            .store()
            .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source("BooleanConstructor"))
            .unwrap();
        let poison = context.store().intrinsic_bootstrap().unwrap().false_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            argument,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.check_source_file(source_file),
            Err(SourceCheckError::Call(argument)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().type_node_links(construction).is_none());
        assert!(context.store().symbol_node_links(constructor).is_none());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn global_date_constructor_materializes_real_signature_and_replays_warm() {
        let library = global_date_constructor_library();
        let source = parse_source_file("const value = new Date();");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_830);
        let source_file = FileId::new(1_831);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (date, owner, declaration, other_declaration, return_annotation, initial_symbols) = {
            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let globals = store.symbol_table(bootstrap.globals).unwrap();
            let date = globals
                .get_source("Date")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("DateConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let declarations = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                .and_then(|signature| store.symbol(signature))
                .and_then(ts_binder::semantic::Symbol::declarations)
                .unwrap();
            assert_eq!(declarations.len(), 2);
            let declaration = declarations
                .iter()
                .copied()
                .find(|declaration| {
                    matches!(
                        &library.arena.get(declaration.node).unwrap().data,
                        NodeData::ConstructSignatureDeclaration(signature)
                            if signature.parameters.nodes.is_empty()
                    )
                })
                .unwrap();
            let other_declaration = declarations
                .iter()
                .copied()
                .find(|other| *other != declaration)
                .unwrap();
            let NodeData::ConstructSignatureDeclaration(signature) =
                &library.arena.get(declaration.node).unwrap().data
            else {
                panic!("DateConstructor must own its real construct declaration")
            };
            let return_annotation = NodeRef::new(
                declaration.arena,
                declaration.file,
                signature.type_.unwrap(),
            );
            assert!(store.declared_type_links(date).is_none());
            assert!(store.declared_type_links(owner).is_none());
            assert!(store.signature_links(declaration).is_none());
            (
                date,
                owner,
                declaration,
                other_declaration,
                return_annotation,
                store.symbol_len(),
            )
        };
        let (construction, constructor) = variable_new(&source, source_file, "value");

        context.check_source_file(source_file).unwrap();

        let store = context.store();
        let instance_type = store
            .declared_type_links(date)
            .and_then(|links| links.declared_type)
            .unwrap();
        let value_type = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .unwrap();
        let value = store.type_payload(value_type).unwrap();
        let TypeData::Interface(interface) = value.data() else {
            panic!("DateConstructor must preserve its real interface identity")
        };
        assert!(!value.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED));
        assert!(!interface.declared_members_resolved);
        assert!(interface.reference.object.structured.signatures.is_none());
        assert!(store.signature_links(other_declaration).is_none());
        let signature = store
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let signature_record = store.signature(signature).unwrap();
        assert_eq!(signature_record.declaration(), Some(declaration));
        assert_eq!(signature_record.flags(), SignatureFlags::CONSTRUCT);
        assert!(signature_record.parameters().is_empty());
        assert_eq!(signature_record.resolved_return_type(), Some(instance_type));
        assert_eq!(signature_record.min_argument_count(), 0);
        assert_eq!(
            authenticated_global_date_constructor_return(store, signature),
            Some(instance_type),
        );
        assert_eq!(store.symbol_len(), initial_symbols);
        assert_eq!(
            store.value_symbol_links(date),
            Some(&ValueSymbolLinks {
                resolved_type: Some(value_type),
                ..ValueSymbolLinks::default()
            }),
        );
        assert_eq!(
            store.type_node_links(return_annotation),
            Some(&TypeNodeLinks {
                resolved_type: Some(instance_type),
                ..TypeNodeLinks::default()
            }),
        );
        let value_annotation = store
            .symbol(date)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .and_then(|declaration| store.source_direct_type_annotation(declaration))
            .unwrap();
        assert_eq!(
            store.symbol_node_links(value_annotation),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(owner),
            }),
        );
        assert_eq!(
            store.symbol_node_links(return_annotation),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(date),
            }),
        );
        assert_eq!(
            store.function_signature_return_annotation(signature),
            Some((return_annotation, false)),
        );
        assert_eq!(
            store.symbol_node_links(constructor),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(date),
            }),
        );
        assert_eq!(
            store.type_node_links(construction),
            Some(&TypeNodeLinks {
                resolved_type: Some(instance_type),
                ..TypeNodeLinks::default()
            }),
        );
        assert_eq!(
            store.signature_links(construction),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            }),
        );
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn reopened_global_date_constructors_preserve_merged_signature_ownership() {
        let library = parse_source_file(concat!(
            "interface Date { toISOString(): string; toJSON(key?: any): string; } ",
            "interface DateConstructor { ",
            "new(): Date; ",
            "new(value: number | string): Date; ",
            "new(year: number, monthIndex: number, date?: number, hours?: number, ",
            "minutes?: number, seconds?: number, ms?: number): Date; ",
            "(): string; readonly prototype: Date; parse(s: string): number; now(): number; ",
            "} declare var Date: DateConstructor;",
        ));
        let extension = parse_source_file(
            "interface DateConstructor { new(value: number | string | Date): Date; }",
        );
        let script_host = parse_source_file(concat!(
            "declare class VarDate { private constructor(); private VarDate_typekey: VarDate; } ",
            "interface DateConstructor { new(vd: VarDate): Date; } ",
            "interface Date { getVarDate: () => VarDate; }",
        ));
        let well_known = parse_source_file(concat!(
            "interface SymbolConstructor { readonly toPrimitive: unique symbol; } ",
            "declare var Symbol: SymbolConstructor; ",
            "interface Date { ",
            "[Symbol.toPrimitive](hint: 'default'): string; ",
            "[Symbol.toPrimitive](hint: 'string'): string; ",
            "[Symbol.toPrimitive](hint: 'number'): number; ",
            "[Symbol.toPrimitive](hint: string): string | number; ",
            "}",
        ));
        let source = parse_source_file(concat!(
            "export class SomeClass { ",
            "constructor(readonly timestamp = new Date()) {} ",
            "}",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(
            extension.diagnostics.is_empty(),
            "{:?}",
            extension.diagnostics
        );
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        assert!(
            script_host.diagnostics.is_empty(),
            "{:?}",
            script_host.diagnostics
        );
        assert!(
            well_known.diagnostics.is_empty(),
            "{:?}",
            well_known.diagnostics
        );
        let library_file = FileId::new(1_870);
        let extension_file = FileId::new(1_871);
        let source_file = FileId::new(1_872);
        let script_host_file = FileId::new(1_881);
        let well_known_file = FileId::new(1_882);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path, default_library, module_state) in [
            (
                &library,
                library_file,
                "\"/lib/es5.d.ts\"",
                true,
                CanonicalModuleState::Script,
            ),
            (
                &extension,
                extension_file,
                "\"/lib/es2015.core.d.ts\"",
                true,
                CanonicalModuleState::Script,
            ),
            (
                &script_host,
                script_host_file,
                "\"/lib/scripthost.d.ts\"",
                true,
                CanonicalModuleState::Script,
            ),
            (
                &well_known,
                well_known_file,
                "\"/lib/es2015.symbol.wellknown.d.ts\"",
                true,
                CanonicalModuleState::Script,
            ),
            (
                &source,
                source_file,
                "\"/project/date.ts\"",
                false,
                CanonicalModuleState::External,
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        default_library,
                        default_library,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (library_file, &library.arena),
                (extension_file, &extension.arena),
                (script_host_file, &script_host.arena),
                (well_known_file, &well_known.arena),
                (source_file, &source.arena),
            ],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: true,
                },
                strict_bind_call_apply: true,
                strict_builtin_iterator_return: true,
                strict_function_types: true,
                strict_property_initialization: true,
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let (date, owner, constructor_symbol) = {
            let store = context.store();
            let globals = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap();
            let date = globals
                .get_source("Date")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("DateConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let constructor = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let record = store.symbol(constructor).unwrap();
            assert_eq!(
                record.flags(),
                SymbolFlags::SIGNATURE | SymbolFlags::TRANSIENT,
            );
            assert_ne!(record.parent(), Some(owner));
            assert_eq!(
                record
                    .parent()
                    .and_then(|parent| store.get_merged_symbol(parent)),
                Some(owner),
            );
            (date, owner, constructor)
        };
        let expression = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(source_file).unwrap();

        let store = context.store();
        let instance = store
            .declared_type_links(date)
            .and_then(|links| links.declared_type)
            .unwrap();
        let signature = store
            .signature_links(expression)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        assert_eq!(
            authenticated_global_date_constructor_return(store, signature),
            Some(instance),
        );
        assert!(exact_global_date_initializer(store, expression, instance));
        assert_eq!(
            store
                .symbol(constructor_symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .map(<[NodeRef]>::len),
            Some(5),
        );
        assert!(store.declared_type_links(owner).is_some());
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn defaulted_constructor_properties_can_preflight_date_initializers_without_publication() {
        let library = global_date_constructor_library();
        let source =
            parse_source_file("class Event { constructor(readonly timestamp = new Date()) {} }");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_840);
        let source_file = FileId::new(1_841);
        let context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (_, source_bound) = context.file(source_file).unwrap();
        let (_, library_bound) = context.file(library_file).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, library_bound),
                (&source.arena, source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let expression = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = plan_direct_default_new(
            &source.arena,
            source_bound,
            context.store(),
            &host,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            expression,
            false,
        )
        .unwrap();

        assert!(matches!(plan.target, SourceNewTarget::GlobalDate(_)));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().type_node_links(expression).is_none());
    }

    #[test]
    fn constructor_date_defaults_reject_poisoned_provider_reference_symbols() {
        for (index, poison_return) in [false, true].into_iter().enumerate() {
            let library = global_date_constructor_library();
            let source = parse_source_file(concat!(
                "class Model { ",
                "constructor(readonly timestamp = new Date()) {} ",
                "}",
            ));
            let offset = u32::try_from(index).unwrap() * 2;
            let library_file = FileId::new(1_873 + offset);
            let source_file = FileId::new(1_874 + offset);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (date, owner, annotation, return_annotation) = {
                let store = context.store();
                let globals = store
                    .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                    .unwrap();
                let date = globals
                    .get_source("Date")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let owner = globals
                    .get_source("DateConstructor")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let annotation = store
                    .symbol(date)
                    .and_then(ts_binder::semantic::Symbol::value_declaration)
                    .and_then(|declaration| store.source_direct_type_annotation(declaration))
                    .unwrap();
                let declaration = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                    .and_then(|symbol| store.symbol(symbol))
                    .and_then(ts_binder::semantic::Symbol::declarations)
                    .and_then(|declarations| {
                        declarations.iter().copied().find(|declaration| {
                            matches!(
                                &library.arena.get(declaration.node).unwrap().data,
                                NodeData::ConstructSignatureDeclaration(signature)
                                    if signature.parameters.nodes.is_empty()
                            )
                        })
                    })
                    .unwrap();
                let return_annotation = store.source_direct_type_annotation(declaration).unwrap();
                (date, owner, annotation, return_annotation)
            };
            let (poisoned_node, wrong_symbol) = if poison_return {
                (return_annotation, owner)
            } else {
                (annotation, date)
            };
            assert!(context.store_mut_for_test().set_symbol_node_links(
                poisoned_node,
                SymbolNodeLinks {
                    resolved_symbol: Some(wrong_symbol),
                },
            ));
            let initializer = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                        source.arena.id(),
                        source_file,
                        node,
                    ))
                })
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                context.check_source_file(source_file),
                Err(SourceCheckError::Class(initializer)),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(context.store().declared_type_links(date).is_none());
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().type_node_links(initializer).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn published_constructor_date_defaults_reject_poisoned_provider_reference_symbols() {
        let library = global_date_constructor_library();
        let source = parse_source_file(concat!(
            "class Model { ",
            "constructor(readonly timestamp = new Date()) {} ",
            "}",
        ));
        let library_file = FileId::new(1_877);
        let source_file = FileId::new(1_878);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let model = class_symbol(&source, source_file, &context, "Model");
        let initializer = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(source_file).unwrap();

        let (date, owner, annotation, return_annotation, date_type, model_type) = {
            let store = context.store();
            let globals = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap();
            let date = globals
                .get_source("Date")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("DateConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let annotation = store
                .symbol(date)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .and_then(|declaration| store.source_direct_type_annotation(declaration))
                .unwrap();
            let signature = store
                .signature_links(initializer)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let return_annotation = store
                .function_signature_return_annotation(signature)
                .map(|(annotation, _)| annotation)
                .unwrap();
            let date_type = store
                .declared_type_links(date)
                .and_then(|links| links.declared_type)
                .unwrap();
            let model_type = store
                .declared_type_links(model)
                .and_then(|links| links.declared_type)
                .unwrap();
            (
                date,
                owner,
                annotation,
                return_annotation,
                date_type,
                model_type,
            )
        };

        assert!(exact_global_date_initializer(
            context.store(),
            initializer,
            date_type,
        ));
        assert_eq!(
            validate_class_heritage_members(context.store(), model_type),
            ClassHeritageMembersValidation::Valid,
        );

        for (node, expected, poison) in
            [(annotation, owner, date), (return_annotation, date, owner)]
        {
            assert!(context.store_mut_for_test().set_symbol_node_links(
                node,
                SymbolNodeLinks {
                    resolved_symbol: Some(poison),
                },
            ));
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(!exact_global_date_initializer(
                context.store(),
                initializer,
                date_type,
            ));
            assert_eq!(
                validate_class_heritage_members(context.store(), model_type),
                ClassHeritageMembersValidation::Malformed,
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );

            assert!(context.store_mut_for_test().set_symbol_node_links(
                node,
                SymbolNodeLinks {
                    resolved_symbol: Some(expected),
                },
            ));
            assert_eq!(
                validate_class_heritage_members(context.store(), model_type),
                ClassHeritageMembersValidation::Valid,
            );
        }
    }

    #[test]
    fn published_constructor_date_defaults_reject_forged_provider_types_and_aliases() {
        let library = global_date_constructor_library();
        let source = parse_source_file(concat!(
            "class Model { ",
            "constructor(readonly timestamp = new Date()) {} ",
            "}",
        ));
        let library_file = FileId::new(1_879);
        let source_file = FileId::new(1_880);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let model = class_symbol(&source, source_file, &context, "Model");
        let initializer = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(source_file).unwrap();

        let (date, owner, annotation, signature, instance, constructor, model_type) = {
            let store = context.store();
            let globals = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap();
            let date = globals
                .get_source("Date")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("DateConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let annotation = store
                .symbol(date)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .and_then(|declaration| store.source_direct_type_annotation(declaration))
                .unwrap();
            let signature = store
                .signature_links(initializer)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let instance = store
                .declared_type_links(date)
                .and_then(|links| links.declared_type)
                .unwrap();
            let constructor = store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let model_type = store
                .declared_type_links(model)
                .and_then(|links| links.declared_type)
                .unwrap();
            (
                date,
                owner,
                annotation,
                signature,
                instance,
                constructor,
                model_type,
            )
        };
        let alias = context.store_mut_for_test().alloc_type_alias(None).unwrap();
        let date_flags = context.store().symbol(date).unwrap().flags();
        let owner_flags = context.store().symbol(owner).unwrap().flags();
        let owner_members = context.store().symbol(owner).unwrap().members();
        assert_ne!(instance, constructor);

        for poison in 0..6 {
            match poison {
                0 => assert!(context.store_mut_for_test().set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(instance),
                        ..TypeNodeLinks::default()
                    },
                )),
                1 => assert!(
                    context
                        .store_mut_for_test()
                        .set_type_alias(instance, Some(alias))
                ),
                2 => assert!(
                    context
                        .store_mut_for_test()
                        .set_type_alias(constructor, Some(alias))
                ),
                3 => assert!(context.store_mut_for_test().set_symbol_flags(
                    owner,
                    owner_flags | SymbolFlags::CLASS,
                    CheckFlags::NONE,
                )),
                4 => assert!(context.store_mut_for_test().set_symbol_flags(
                    date,
                    date_flags | SymbolFlags::VALUE_MODULE,
                    CheckFlags::NONE,
                )),
                5 => assert!(context.store_mut_for_test().set_symbol_relationships(
                    owner,
                    owner_members,
                    None,
                    Some(date),
                    None,
                )),
                _ => unreachable!("Date provider poison cases are bounded"),
            }
            let before = (
                context.store().type_len(),
                context.store().type_alias_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                authenticated_global_date_constructor_return(context.store(), signature),
                None,
                "case {poison}",
            );
            assert!(
                !exact_global_date_initializer(context.store(), initializer, instance),
                "case {poison}",
            );
            assert_eq!(
                validate_class_heritage_members(context.store(), model_type),
                ClassHeritageMembersValidation::Malformed,
                "case {poison}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().type_alias_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "case {poison}",
            );

            match poison {
                0 => assert!(context.store_mut_for_test().set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(constructor),
                        ..TypeNodeLinks::default()
                    },
                )),
                1 => assert!(context.store_mut_for_test().set_type_alias(instance, None)),
                2 => assert!(
                    context
                        .store_mut_for_test()
                        .set_type_alias(constructor, None)
                ),
                3 => assert!(context.store_mut_for_test().set_symbol_flags(
                    owner,
                    owner_flags,
                    CheckFlags::NONE,
                )),
                4 => assert!(context.store_mut_for_test().set_symbol_flags(
                    date,
                    date_flags,
                    CheckFlags::NONE,
                )),
                5 => assert!(context.store_mut_for_test().set_symbol_relationships(
                    owner,
                    owner_members,
                    None,
                    None,
                    None,
                )),
                _ => unreachable!("Date provider poison cases are bounded"),
            }
            assert_eq!(
                authenticated_global_date_constructor_return(context.store(), signature),
                Some(instance),
                "case {poison}",
            );
            assert_eq!(
                validate_class_heritage_members(context.store(), model_type),
                ClassHeritageMembersValidation::Valid,
                "case {poison}",
            );
        }
    }

    #[test]
    fn global_date_overloads_use_later_groups_and_preserve_group_order() {
        for (index, declarations, selected) in [
            (
                0,
                concat!(
                    "interface DateConstructor { new(): string; } ",
                    "interface DateConstructor { new(): Date; } ",
                ),
                1,
            ),
            (
                1,
                concat!(
                    "interface DateConstructor { new(): Date; new(): string; } ",
                    "interface DateConstructor { new(value: number): string; } ",
                ),
                0,
            ),
        ] {
            let library = parse_source_file(&format!(
                "interface Date {{}} {declarations} declare var Date: DateConstructor;",
            ));
            let source = parse_source_file("const value = new Date();");
            let library_file = FileId::new(1_905 + index * 2);
            let source_file = FileId::new(1_906 + index * 2);
            let declarations = library
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ConstructSignature).then_some(NodeRef::new(
                        library.arena.id(),
                        library_file,
                        node,
                    ))
                })
                .collect::<Vec<_>>();
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (expression, _) = variable_new(&source, source_file, "value");

            context.check_source_file(source_file).unwrap();

            let signature = context
                .store()
                .signature_links(expression)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert_eq!(
                context.store().signature(signature).unwrap().declaration(),
                Some(declarations[selected]),
            );
            let instance =
                authenticated_global_date_constructor_return(context.store(), signature).unwrap();
            let store = context.store();
            let date = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source("Date"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            assert_eq!(
                store
                    .declared_type_links(date)
                    .and_then(|links| links.declared_type),
                Some(instance),
            );
            assert_eq!(
                store
                    .type_node_links(expression)
                    .and_then(|links| links.resolved_type),
                Some(instance),
            );
            let warm = (context.store().type_len(), context.store().signature_len());
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (context.store().type_len(), context.store().signature_len()),
                warm
            );
        }
    }

    #[test]
    fn global_date_overload_competitors_reject_before_cache_publication() {
        for overload in [
            "new(): string;",
            "new(value?: number): string;",
            "new(...values: number[]): string;",
            "new(value: void): string;",
            "new<Value>(): Date;",
        ] {
            let library = parse_source_file(&format!(
                concat!(
                    "interface Date {{}} ",
                    "interface DateConstructor {{ new(): Date; }} ",
                    "interface DateConstructor {{ {} }} ",
                    "declare var Date: DateConstructor;",
                ),
                overload,
            ));
            let source = parse_source_file("const value = new Date();");
            let library_file = FileId::new(1_911);
            let source_file = FileId::new(1_912);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let (expression, _) = variable_new(&source, source_file, "value");
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    context.check_source_file(source_file),
                    Err(super::super::SourceCheckError::Unsupported(_))
                ),
                "{overload}"
            );

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "{overload}",
            );
            assert!(context.store().type_node_links(expression).is_none());
            assert!(context.store().signature_links(expression).is_none());
        }
    }

    #[test]
    fn global_date_defaults_reject_forged_interface_this_type_graphs() {
        let library = parse_source_file(concat!(
            "interface Date { self: this; } ",
            "interface DateConstructor { self: this; new(): Date; readonly prototype: Date; } ",
            "declare var Date: DateConstructor;",
        ));
        let source =
            parse_source_file("class Model { constructor(readonly timestamp = new Date()) {} }");
        let library_file = FileId::new(1_899);
        let source_file = FileId::new(1_900);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let initializer = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        context.check_source_file(source_file).unwrap();
        let signature = context
            .store()
            .signature_links(initializer)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let instance = context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        for name in ["Date", "DateConstructor"] {
            let store = context.store();
            let owner = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let type_ = store
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let TypeData::Interface(interface) = store.type_payload(type_).unwrap().data() else {
                panic!("{name} must retain its declared interface")
            };
            let this_type = interface.this_type.unwrap();
            let alias = context.store_mut_for_test().alloc_type_alias(None).unwrap();
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_alias(this_type, Some(alias))
            );
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            );

            assert_eq!(
                authenticated_global_date_constructor_return(context.store(), signature),
                None
            );
            assert!(!exact_global_date_initializer(
                context.store(),
                initializer,
                instance
            ));
            assert!(context.recheck_source_file(source_file).is_err());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().clone(),
                ),
                before,
                "{name}",
            );
            assert!(context.store_mut_for_test().set_type_alias(this_type, None));
            assert_eq!(
                authenticated_global_date_constructor_return(context.store(), signature),
                Some(instance)
            );
        }
    }

    #[test]
    fn global_date_signatures_reject_erased_parameters_and_wrong_return_names() {
        let library = parse_source_file(concat!(
            "interface Date {} interface Other {} ",
            "interface DateConstructor { ",
            "new(): Date; new(value: number): Date; new<Value>(): Date; new(): Other; ",
            "readonly prototype: Date; ",
            "} declare var Date: DateConstructor;",
        ));
        let source = parse_source_file("const value = new Date();");
        let library_file = FileId::new(1_883);
        let source_file = FileId::new(1_884);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let (construction, constructor) = variable_new(&source, source_file, "value");
        context.check_source_file(source_file).unwrap();

        let date = context
            .store()
            .symbol_node_links(constructor)
            .and_then(|links| links.resolved_symbol)
            .unwrap();
        let instance = context
            .store()
            .type_node_links(construction)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let original = context
            .store()
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let mut rejected = 0;
        for (node, record) in library.arena.iter() {
            let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(library.arena.id(), library_file, node);
            if context.store().signature(original).unwrap().declaration() == Some(declaration) {
                continue;
            }
            let annotation =
                NodeRef::new(library.arena.id(), library_file, signature.type_.unwrap());
            let store = context.store_mut_for_test();
            let forged = store
                .alloc_signature(
                    SignatureFlags::CONSTRUCT,
                    Some(declaration),
                    Vec::new(),
                    None,
                    Vec::new(),
                    Some(instance),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(instance),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_symbol_node_links(
                annotation,
                SymbolNodeLinks {
                    resolved_symbol: Some(date),
                },
            ));
            for node in [declaration, construction] {
                assert!(store.set_signature_links(
                    node,
                    SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolved(forged),
                        ..SignatureLinks::default()
                    },
                ));
            }
            assert!(store.set_function_signature_return_annotation(forged, annotation, false));
            let before = (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                authenticated_global_date_constructor_return(store, forged),
                None
            );
            assert!(!exact_global_date_initializer(
                store,
                construction,
                instance
            ));
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
            rejected += 1;
        }
        assert_eq!(rejected, 3);
        assert!(context.store_mut_for_test().set_signature_links(
            construction,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(original),
                ..SignatureLinks::default()
            },
        ));
        assert!(exact_global_date_initializer(
            context.store(),
            construction,
            instance
        ));
    }

    #[test]
    fn global_date_constructor_rejects_forged_global_and_signature_caches() {
        for poison in 0..3 {
            let library = global_date_constructor_library();
            let source = parse_source_file("const value = new Date();");
            let library_file = FileId::new(1_832 + poison * 2);
            let source_file = FileId::new(1_833 + poison * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);

            context.check_source_file(source_file).unwrap();

            let (construction, _) = variable_new(&source, source_file, "value");
            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let (date, owner, globals) = {
                let store = context.store();
                let globals = store.intrinsic_bootstrap().unwrap().globals;
                let symbols = store.symbol_table(globals).unwrap();
                (
                    symbols
                        .get_source("Date")
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        .unwrap(),
                    symbols
                        .get_source("DateConstructor")
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        .unwrap(),
                    globals,
                )
            };
            match poison {
                0 => {
                    assert!(context.store_mut_for_test().set_signature_flags(
                        signature,
                        SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT,
                    ));
                }
                1 => {
                    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(signature, Some(string))
                    );
                }
                2 => {
                    assert_eq!(
                        context.store_mut_for_test().insert_symbol(
                            globals,
                            EscapedName::source("Date"),
                            owner,
                        ),
                        Some(Some(date)),
                    );
                }
                _ => unreachable!("global Date poison cases are bounded"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                authenticated_global_date_constructor_return(context.store(), signature),
                None,
                "case {poison}",
            );

            assert!(
                context.recheck_source_file(source_file).is_err(),
                "case {poison}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "case {poison}",
            );
        }
    }

    #[test]
    fn global_promise_executor_preserves_generic_identity_and_reports_jsdoc_hint() {
        let base = global_promise_base_library();
        let library = global_promise_constructor_library();
        let source = parse_javascript_source_file("new Promise((resolve) => resolve());");
        assert!(base.diagnostics.is_empty(), "{:?}", base.diagnostics);
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let base_file = FileId::new(1_850);
        let library_file = FileId::new(1_851);
        let source_file = FileId::new(1_852);
        let mut context = global_promise_constructor_context(
            &base,
            &library,
            &source,
            base_file,
            library_file,
            source_file,
        );
        let (promise, owner, declaration) = {
            let store = context.store();
            let globals = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .unwrap();
            let promise = globals
                .get_source("Promise")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let owner = globals
                .get_source("PromiseConstructor")
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let declaration = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                .and_then(|signature| store.symbol(signature))
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first())
                .copied()
                .unwrap();
            assert!(store.declared_type_links(promise).is_none());
            assert!(store.declared_type_links(owner).is_none());
            assert!(store.signature_links(declaration).is_none());
            (promise, owner, declaration)
        };
        let construction = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        let executor = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(source_file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected the missing Promise JSDoc hint")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2810);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Expected 1 argument, but got 0. 'new Promise()' needs a JSDoc ",
                "hint to produce a 'resolve' that can be called without arguments.",
            ),
        );
        let store = context.store();
        let promise_target = store
            .declared_type_links(promise)
            .and_then(|links| links.declared_type)
            .unwrap();
        let instance = store
            .type_node_links(construction)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let unknown = store.intrinsic_bootstrap().unwrap().unknown_type;
        let reference = validate_direct_generic_reference(store, instance).unwrap();
        assert_eq!(reference.target, promise_target);
        assert_eq!(reference.type_arguments, vec![unknown]);
        let value = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .and_then(|type_| store.type_payload(type_))
            .unwrap();
        assert!(!value.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED));
        let base = store
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let selected = store
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        assert_ne!(base, selected);
        assert_eq!(store.signature(selected).unwrap().target(), Some(base));
        let executor_type = store
            .type_node_links(executor)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provenance = store.source_callable_provenance(executor_type).unwrap();
        assert!(provenance.contextual_target.is_some());
        assert!(provenance.contextual_variable.is_none());
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.cached_signature_len(),
            store.checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().cached_signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert_eq!(context.diagnostics().as_slice().len(), 1);
    }

    #[test]
    fn global_promise_constructor_rejects_forged_global_and_signature_caches() {
        for poison in 0..3 {
            let base_library = global_promise_base_library();
            let library = global_promise_constructor_library();
            let source = parse_javascript_source_file("new Promise((resolve) => resolve());");
            let base_file = FileId::new(1_860 + poison * 3);
            let library_file = FileId::new(1_861 + poison * 3);
            let source_file = FileId::new(1_862 + poison * 3);
            let mut context = global_promise_constructor_context(
                &base_library,
                &library,
                &source,
                base_file,
                library_file,
                source_file,
            );

            context.check_source_file(source_file).unwrap();

            let (promise, owner, globals, base, selected) = {
                let store = context.store();
                let globals = store.intrinsic_bootstrap().unwrap().globals;
                let symbols = store.symbol_table(globals).unwrap();
                let promise = symbols
                    .get_source("Promise")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let owner = symbols
                    .get_source("PromiseConstructor")
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap();
                let declaration = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
                    .and_then(|signature| store.symbol(signature))
                    .and_then(ts_binder::semantic::Symbol::declarations)
                    .and_then(|declarations| declarations.first())
                    .copied()
                    .unwrap();
                let base = store
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap();
                let unknown = store.intrinsic_bootstrap().unwrap().unknown_type;
                let CachedSignatureLookup::Hit(selected) =
                    store.cached_signature(base, type_list_key(&[unknown]), &[unknown])
                else {
                    panic!("expected the selected Promise signature")
                };
                (promise, owner, globals, base, selected)
            };
            match poison {
                0 => {
                    assert!(context.store_mut_for_test().set_signature_flags(
                        base,
                        SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT,
                    ));
                }
                1 => {
                    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(selected, Some(string))
                    );
                }
                2 => {
                    assert_eq!(
                        context.store_mut_for_test().insert_symbol(
                            globals,
                            EscapedName::source("Promise"),
                            owner,
                        ),
                        Some(Some(promise)),
                    );
                }
                _ => unreachable!("global Promise poison cases are bounded"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                context.recheck_source_file(source_file).is_err(),
                "case {poison}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "case {poison}",
            );
        }
    }

    #[test]
    fn global_array_constructors_preserve_real_overloads_and_warm_instantiations() {
        let library = global_array_constructor_library();
        let source = parse_source_file(concat!(
            "const empty = new Array(); ",
            "const length = new Array(1); ",
            "const strings = new Array('hi', 'bye'); ",
            "const numbers = new Array<number>(1, 2); ",
            "const typedLength = new Array<string>(1);",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_840);
        let source_file = FileId::new(1_841);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);
        let globals = context.global_types().clone();

        context.check_source_file(source_file).unwrap();

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        for (name, expected) in [
            ("empty", bootstrap.any_type),
            ("length", bootstrap.any_type),
            ("strings", bootstrap.string_type),
            ("numbers", bootstrap.number_type),
            ("typedLength", bootstrap.string_type),
        ] {
            let (construction, constructor) = variable_new(&source, source_file, name);
            let type_ = context
                .store()
                .type_node_links(construction)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(&globals, type_)
                    .unwrap(),
                Some(expected),
                "{name}",
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol)
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .signature_links(construction)
                    .and_then(|links| links.resolved_signature.signature())
                    .is_some()
            );
        }
        let owner = context
            .store()
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source("ArrayConstructor"))
            .and_then(|owner| context.store().get_merged_symbol(owner))
            .unwrap();
        let value = context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .and_then(|type_| context.store().type_payload(type_))
            .unwrap();
        let TypeData::Interface(interface) = value.data() else {
            panic!("ArrayConstructor must retain its real interface identity")
        };
        assert!(!value.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED));
        assert!(!interface.declared_members_resolved);
        assert!(interface.reference.object.structured.signatures.is_none());
        let declarations = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
            .and_then(|constructor| context.store().symbol(constructor))
            .and_then(|constructor| constructor.declarations())
            .unwrap();
        assert_eq!(declarations.len(), 3);
        assert!(declarations.iter().all(|declaration| {
            context
                .store()
                .signature_links(*declaration)
                .and_then(|links| links.resolved_signature.signature())
                .is_some()
        }));
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().cached_signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().cached_signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn global_array_object_items_preserve_fresh_arguments_and_canonical_empty_elements() {
        let library = global_array_constructor_library();
        let source = parse_source_file(concat!(
            "const first = new Array({}); ",
            "const second = new Array({}); ",
            "const explicit = new Array<any>({});",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_844);
        let source_file = FileId::new(1_845);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);

        context.check_source_file(source_file).unwrap();

        let (empty, any) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.empty_type_literal_type, bootstrap.any_type)
        };
        let mut object_types = Vec::new();
        for (name, expected_element) in [("first", empty), ("second", empty), ("explicit", any)] {
            let (construction, _) = variable_new(&source, source_file, name);
            let instance = context
                .store()
                .type_node_links(construction)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(context.global_types(), instance)
                    .unwrap(),
                Some(expected_element),
            );
            let NodeData::NewExpression(expression) =
                &source.arena.get(construction.node).unwrap().data
            else {
                panic!("the selected variable must retain its Array construction")
            };
            let [object] = expression.arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("the Array items overload must retain one empty object argument")
            };
            let object = NodeRef::new(source.arena.id(), source_file, *object);
            let owner = context.file(source_file).unwrap().1.symbol(object).unwrap();
            let object_type = context
                .store()
                .type_node_links(object)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let object_record = context.store().type_payload(object_type).unwrap();
            assert_eq!(object_record.symbol(), Some(owner));
            assert_eq!(
                object_record.object_flags(),
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
                    | ObjectFlags::MEMBERS_RESOLVED,
            );
            let TypeData::Object(object_record) = object_record.data() else {
                panic!("the Array argument must retain a fresh source object")
            };
            assert!(
                context
                    .store()
                    .symbol_table(object_record.structured.members.unwrap())
                    .unwrap()
                    .is_empty()
            );
            assert_ne!(object_type, empty);
            object_types.push(object_type);
        }
        assert_ne!(object_types[0], object_types[1]);
        assert_ne!(object_types[1], object_types[2]);
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().cached_signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(source_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().cached_signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn global_array_object_items_reject_nonempty_or_forged_object_arguments() {
        let library = global_array_constructor_library();
        let nonempty = parse_source_file("const value = new Array({ value: 1 });");
        let mut context = global_object_constructor_context(
            &library,
            &nonempty,
            FileId::new(1_846),
            FileId::new(1_847),
        );
        let (construction, _) = variable_new(&nonempty, FileId::new(1_847), "value");

        assert!(context.check_source_file(FileId::new(1_847)).is_err());
        assert!(context.store().type_node_links(construction).is_none());
        assert!(context.store().signature_links(construction).is_none());

        let source = parse_source_file("const value = new Array({});");
        let source_file = FileId::new(1_849);
        let mut context =
            global_object_constructor_context(&library, &source, FileId::new(1_848), source_file);
        let (construction, _) = variable_new(&source, source_file, "value");
        let NodeData::NewExpression(expression) =
            &source.arena.get(construction.node).unwrap().data
        else {
            panic!("the selected variable must retain its Array construction")
        };
        let object = NodeRef::new(
            source.arena.id(),
            source_file,
            expression.arguments.as_ref().unwrap().nodes[0],
        );
        let owner = context.file(source_file).unwrap().1.symbol(object).unwrap();
        let parent = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_symbol;
        assert!(context.store_mut_for_test().set_symbol_relationships(
            owner,
            None,
            None,
            Some(parent),
            None,
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(context.check_source_file(source_file).is_err());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().type_node_links(object).is_none());
        assert!(context.store().type_node_links(construction).is_none());
    }

    #[test]
    fn global_array_constructors_work_on_contextual_assignment_right_sides() {
        let library = global_array_constructor_library();
        let source = parse_source_file(concat!(
            "var text: string[]; ",
            "text = new Array(1); ",
            "text = new Array('hi', 'bye'); ",
            "text = new Array<string>('hi', 'bye'); ",
            "var numeric: number[]; ",
            "numeric = new Array(1); ",
            "numeric = new Array(1, 2); ",
            "numeric = new Array<number>(1, 2);",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_842);
        let source_file = FileId::new(1_843);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);

        context.check_source_file(source_file).unwrap();

        assert!(context.diagnostics().is_empty());
        let constructions = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(constructions.len(), 6);
        assert!(constructions.iter().all(|construction| {
            context
                .store()
                .signature_links(*construction)
                .and_then(|links| links.resolved_signature.signature())
                .is_some()
        }));
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().cached_signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().cached_signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn declared_construct_signatures_publish_real_returns_and_replay_warm() {
        for (source, returns_number, has_argument) in [
            (
                "declare const factory: { new(): string }; const result = new factory();",
                false,
                false,
            ),
            (
                "declare const factory: { new(value: number): string }; const result = new factory(1);",
                false,
                true,
            ),
            (
                "declare const factory: { (): number; new(): string }; const result = new factory();",
                false,
                false,
            ),
            (
                concat!(
                    "declare const factory: { ",
                    "new(value: number): string; ",
                    "(value: string): number ",
                    "}; const result = new factory(1);",
                ),
                false,
                true,
            ),
            (
                concat!(
                    "interface Factory { new(value: string): number; } ",
                    "declare let factory: Factory; ",
                    "const result = new factory(\"ready\");",
                ),
                true,
                true,
            ),
            (
                concat!(
                    "interface Factory { ",
                    "(value: number): string; ",
                    "new(value: string): number; ",
                    "} ",
                    "declare let factory: Factory; ",
                    "const result = new factory(\"ready\");",
                ),
                true,
                true,
            ),
            (
                concat!(
                    "type Factory = { ",
                    "new(value: number): string; ",
                    "new(value: string): number ",
                    "}; ",
                    "declare var factory: Factory; ",
                    "const result = new factory(\"ready\");",
                ),
                true,
                true,
            ),
            (
                concat!(
                    "type Factory = { ",
                    "new(value: number): string; ",
                    "(value: number): string; ",
                    "new(value: string): number ",
                    "}; ",
                    "declare var factory: Factory; ",
                    "const result = new factory(\"ready\");",
                ),
                true,
                true,
            ),
            (
                "declare const factory: { new(value: any): number }; const result = new factory(1);",
                true,
                true,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_810);
            let mut context = context(&parsed, file);
            let (annotation, owner) = ambient_constructor(&parsed, file, &context, "factory");
            let (construction, constructor) = variable_new(&parsed, file, "result");

            context.check_source_file(file).unwrap();

            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let expected = if returns_number {
                bootstrap.number_type
            } else {
                bootstrap.string_type
            };
            let value = store
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let record = store.signature(signature).unwrap();
            assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
            assert!(!record.flags().intersects(SignatureFlags::ABSTRACT));
            assert_eq!(record.resolved_return_type(), Some(expected));
            assert_eq!(record.parameters().len(), usize::from(has_argument));
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
            );
            assert_eq!(
                store
                    .type_node_links(constructor)
                    .and_then(|links| links.resolved_type),
                Some(value),
            );
            assert_eq!(
                store
                    .type_node_links(construction)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
            assert!(
                matches!(
                    validate_stored_callable_set(store, value),
                    StoredCallableSetValidation::Valid {
                        family: CallableFamily::DeclaredCallSignatures,
                        ..
                    }
                ),
                "{source}",
            );
            assert!(
                context.diagnostics().is_empty(),
                "{source}: {:?}",
                context.diagnostics()
            );
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
                "{source}",
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn named_constructor_values_select_distinct_returns_without_a_prototype() {
        let parsed = parse_source_file(concat!(
            "interface Factory { new(value: string): string; new(value: number): number; label: string; } ",
            "declare const Build: Factory; ",
            "const text = new Build(\"ready\"); const count = new Build(1);",
        ));
        let file = FileId::new(1_983);
        let mut context = context(&parsed, file);
        let (text, text_value) = variable_new(&parsed, file, "text");
        let (count, count_value) = variable_new(&parsed, file, "count");
        context.check_source_file(file).unwrap();
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let text_signature = store
            .signature_links(text)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let count_signature = store
            .signature_links(count)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_ne!(text_signature, count_signature);
        assert_eq!(
            store.type_node_links(text).unwrap().resolved_type,
            Some(bootstrap.string_type)
        );
        assert_eq!(
            store.type_node_links(count).unwrap().resolved_type,
            Some(bootstrap.number_type)
        );
        assert_eq!(
            store.type_node_links(text_value),
            store.type_node_links(count_value)
        );
        assert_eq!(
            store
                .signature(text_signature)
                .unwrap()
                .resolved_return_type(),
            Some(bootstrap.string_type)
        );
        assert_eq!(
            store
                .signature(count_signature)
                .unwrap()
                .resolved_return_type(),
            Some(bootstrap.number_type)
        );
        assert!(context.diagnostics().is_empty());
        let warm = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            warm
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn declared_class_constructor_unions_preserve_identity_abstract_diagnostics_and_warm_replay() {
        for (source, abstract_union) in [
            (
                concat!(
                    "class First {} class Second {} ",
                    "declare const factory: typeof First | typeof Second; ",
                    "const result = new factory();",
                ),
                false,
            ),
            (
                concat!(
                    "class First {} class Second {} ",
                    "type Factory = typeof First | typeof Second; ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                false,
            ),
            (
                concat!(
                    "abstract class First { value!: string; } ",
                    "class Second {} ",
                    "type Factory = typeof First | typeof Second; ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                true,
            ),
            (
                concat!(
                    "abstract class First { value!: string; } ",
                    "abstract class Second { other!: number; } ",
                    "type Factory = typeof First | typeof Second; ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                true,
            ),
            (
                concat!(
                    "abstract class Abstract { value!: string; } ",
                    "class First {} class Second {} ",
                    "type Concrete = typeof First | typeof Second; ",
                    "type Factory = typeof Abstract | Concrete; ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                true,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_860);
            let mut context = context(&parsed, file);
            let (annotation, owner) = ambient_constructor(&parsed, file, &context, "factory");
            let (construction, constructor) = variable_new(&parsed, file, "result");

            context.check_source_file(file).unwrap();

            let store = context.store();
            let value = store
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let TypeData::Union(candidates) = store.type_payload(value).unwrap().data() else {
                panic!("{source} must retain the canonical constructor union")
            };
            assert!(candidates.union.types.len() >= 2, "{source}");
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let result = store
                .type_node_links(construction)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
                "{source}",
            );
            assert_eq!(
                store
                    .type_node_links(constructor)
                    .and_then(|links| links.resolved_type),
                Some(value),
                "{source}",
            );
            assert_eq!(
                store
                    .signature(signature)
                    .and_then(Signature::resolved_return_type),
                Some(result),
                "{source}",
            );
            if abstract_union {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                assert_eq!(signature, bootstrap.unknown_signature, "{source}");
                assert_eq!(result, bootstrap.error_type, "{source}");
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("{source} must reject an abstract constructor constituent")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2511, "{source}");
                assert!(diagnostic.diagnostic.arguments.is_empty(), "{source}");
                assert_eq!(diagnostic.node, Some(construction), "{source}");
            } else {
                assert!(context.diagnostics().is_empty(), "{source}");
                let composite = store.signature(signature).unwrap().composite().unwrap();
                let constructors = candidates
                    .union
                    .types
                    .iter()
                    .map(|candidate| {
                        let symbol = store.type_payload(*candidate).unwrap().symbol().unwrap();
                        authenticated_class_constructor_value(store, symbol)
                            .unwrap()
                            .1
                    })
                    .collect::<Vec<_>>();
                assert!(composite.is_union(), "{source}");
                assert_eq!(composite.signatures(), constructors, "{source}");
                let TypeData::Union(instances) = store.type_payload(result).unwrap().data() else {
                    panic!("{source} must keep every concrete instance type")
                };
                assert_eq!(instances.union.types.len(), constructors.len(), "{source}");
                for constructor in constructors {
                    assert!(
                        instances.union.types.contains(
                            &store
                                .signature(constructor)
                                .unwrap()
                                .resolved_return_type()
                                .unwrap()
                        )
                    );
                }
            }
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().clone(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn abstract_class_union_instantiation_reports_only_abstract_constructor_unions() {
        let parsed = parse_source_file(concat!(
            "class ConcreteA {} class ConcreteB {} ",
            "abstract class AbstractA { a: string; } ",
            "abstract class AbstractB { b: string; } ",
            "type Abstracts = typeof AbstractA | typeof AbstractB; ",
            "type Concretes = typeof ConcreteA | typeof ConcreteB; ",
            "type All = Concretes | Abstracts; ",
            "declare const mixed: All; ",
            "declare const abstractOnly: Abstracts; ",
            "declare const concreteOnly: Concretes; ",
            "new mixed(); new abstractOnly(); new concreteOnly();",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_863);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let constructions = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(constructions.len(), 3);
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, construction) in diagnostics.iter().zip(&constructions) {
            assert_eq!(diagnostic.diagnostic.code(), 2511);
            assert!(diagnostic.diagnostic.arguments.is_empty());
            assert_eq!(diagnostic.node, Some(*construction));
        }
        assert!(constructions.iter().all(|construction| {
            context
                .store()
                .signature_links(*construction)
                .and_then(|links| links.resolved_signature.signature())
                .is_some()
        }));
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().clone(),
        );

        context.recheck_source_file(file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }

    #[test]
    fn class_constructor_array_callbacks_preserve_abstract_diagnostics_and_warm_identity() {
        let library = global_array_map_constructor_library();
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        for (index, (classes, expected_diagnostics)) in [
            (
                concat!(
                    "class First {} class Second {} ",
                    "[First, Second].map(cls => new cls());",
                ),
                0,
            ),
            (
                concat!(
                    "class Concrete {} ",
                    "abstract class Abstract { value!: string; } ",
                    "[Concrete, Abstract].map(cls => new cls());",
                ),
                1,
            ),
            (
                concat!(
                    "abstract class First { value!: string; } ",
                    "abstract class Second { other!: number; } ",
                    "[First, Second].map(cls => new cls());",
                ),
                1,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parse_source_file(classes);
            assert!(
                source.diagnostics.is_empty(),
                "{classes}: {:?}",
                source.diagnostics
            );
            let library_file = FileId::new(1_870 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(1_871 + u32::try_from(index * 2).unwrap());
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let construction = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                        source.arena.id(),
                        source_file,
                        node,
                    ))
                })
                .unwrap();

            context.check_source_file(source_file).unwrap();

            assert_eq!(
                context.diagnostics().len(),
                expected_diagnostics,
                "{classes}"
            );
            if expected_diagnostics != 0 {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("{classes} must retain one abstract constructor diagnostic")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2511);
                assert!(diagnostic.diagnostic.arguments.is_empty());
                assert_eq!(diagnostic.node, Some(construction));
            }
            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let instance = context
                .store()
                .type_node_links(construction)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .signature(signature)
                    .and_then(Signature::resolved_return_type),
                Some(instance),
            );
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            );

            context.recheck_source_file(source_file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().clone(),
                ),
                warm,
                "{classes}",
            );
        }
    }

    #[test]
    fn abstract_class_union_fixture_preserves_top_level_and_array_callback_diagnostics() {
        let library = global_array_map_constructor_library();
        let source = parse_source_file(concat!(
            "class ConcreteA {} class ConcreteB {} ",
            "abstract class AbstractA { a: string; } ",
            "abstract class AbstractB { b: string; } ",
            "type Abstracts = typeof AbstractA | typeof AbstractB; ",
            "type Concretes = typeof ConcreteA | typeof ConcreteB; ",
            "type ConcretesOrAbstracts = Concretes | Abstracts; ",
            "declare const cls1: ConcretesOrAbstracts; ",
            "declare const cls2: Abstracts; ",
            "declare const cls3: Concretes; ",
            "new cls1(); new cls2(); new cls3(); ",
            "[ConcreteA, AbstractA, AbstractB].map(cls => new cls()); ",
            "[AbstractA, AbstractB, ConcreteA].map(cls => new cls()); ",
            "[ConcreteA, ConcreteB].map(cls => new cls()); ",
            "[AbstractA, AbstractB].map(cls => new cls());",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(1_890);
        let source_file = FileId::new(1_891);
        let mut context =
            global_object_constructor_context(&library, &source, library_file, source_file);

        context.check_source_file(source_file).unwrap();

        let constructions = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(constructions.len(), 7);
        let expected = [
            constructions[0],
            constructions[1],
            constructions[3],
            constructions[4],
            constructions[6],
        ];
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), expected.len());
        for (diagnostic, construction) in diagnostics.iter().zip(expected) {
            assert_eq!(diagnostic.diagnostic.code(), 2511);
            assert!(diagnostic.diagnostic.arguments.is_empty());
            assert_eq!(diagnostic.node, Some(construction));
        }
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().clone(),
        );

        context.recheck_source_file(source_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }

    #[test]
    fn constructor_union_callbacks_reject_forged_parameter_and_class_caches() {
        for poison in 0..2 {
            let library = global_array_map_constructor_library();
            let source = parse_source_file(concat!(
                "class First {} class Second {} ",
                "[First, Second].map(cls => new cls());",
            ));
            let library_file = FileId::new(1_880 + poison * 2);
            let source_file = FileId::new(1_881 + poison * 2);
            let mut context =
                global_object_constructor_context(&library, &source, library_file, source_file);
            let construction = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                        source.arena.id(),
                        source_file,
                        node,
                    ))
                })
                .unwrap();
            match poison {
                0 => {
                    let parameter = source
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::Parameter).then_some(NodeRef::new(
                                source.arena.id(),
                                source_file,
                                node,
                            ))
                        })
                        .unwrap();
                    let symbol = context
                        .file(source_file)
                        .unwrap()
                        .1
                        .symbol(parameter)
                        .unwrap();
                    let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(context.store_mut_for_test().set_value_symbol_links(
                        symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(wrong),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                1 => {
                    let first = class_symbol(&source, source_file, &context, "First");
                    assert!(context.store_mut_for_test().set_symbol_flags(
                        first,
                        SymbolFlags::CLASS | SymbolFlags::INTERFACE,
                        CheckFlags::NONE,
                    ));
                }
                _ => unreachable!("only callback parameters and class owners are poisoned"),
            }
            let state = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                context.check_source_file(source_file).is_err(),
                "case {poison}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                state,
                "case {poison}",
            );
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().signature_links(construction).is_none());
        }
    }

    #[test]
    fn forged_class_union_constructor_signature_rejects_before_new_publication() {
        for poison in 0..2 {
            let parsed = parse_source_file(concat!(
                "class First {} class Second {} ",
                "type Factory = typeof First | typeof Second; ",
                "declare const factory: Factory; ",
                "const result = new factory();",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(1_861 + poison);
            let mut context = context(&parsed, file);
            let (annotation, _) = ambient_constructor(&parsed, file, &context, "factory");
            let (construction, constructor) = variable_new(&parsed, file, "result");
            context.get_type_from_type_node(annotation).unwrap();
            let class = class_symbol(&parsed, file, &context, "First");
            let (_, signature) =
                authenticated_class_constructor_value(context.store(), class).unwrap();
            match poison {
                0 => assert!(context.store_mut_for_test().set_signature_flags(
                    signature,
                    SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT,
                )),
                1 => {
                    let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(signature, Some(wrong))
                    );
                }
                _ => unreachable!("only class constructor flags and return values are forged"),
            }
            let state = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                context.check_source_file(file).is_err(),
                "poison case {poison}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                state,
                "poison case {poison}",
            );
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().signature_links(construction).is_none());
            assert!(context.store().symbol_node_links(constructor).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn constructor_union_results_reject_forged_returns_and_composite_members() {
        for poison in 0..3 {
            let parsed = parse_source_file(concat!(
                "class First {} class Second {} ",
                "type Factory = typeof First | typeof Second; ",
                "declare const factory: Factory; const result = new factory();",
            ));
            let file = FileId::new(1_895 + poison);
            let mut context = context(&parsed, file);
            let (construction, _) = variable_new(&parsed, file, "result");
            context.check_source_file(file).unwrap();
            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let members = context
                .store()
                .signature(signature)
                .unwrap()
                .composite()
                .unwrap()
                .signatures()
                .to_vec();
            match poison {
                0 => {
                    let first_instance = context
                        .store()
                        .signature(members[0])
                        .unwrap()
                        .resolved_return_type()
                        .unwrap();
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(signature, Some(first_instance),)
                    );
                    assert!(context.store_mut_for_test().set_type_node_links(
                        construction,
                        TypeNodeLinks {
                            resolved_type: Some(first_instance),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                1 | 2 => {
                    let replacement = if poison == 1 {
                        vec![members[0], members[0]]
                    } else {
                        vec![members[1], members[0]]
                    };
                    let composite = context
                        .store()
                        .create_composite_signature(true, replacement)
                        .unwrap();
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_composite(signature, Some(composite))
                    );
                }
                _ => unreachable!("only constructor returns and composite members are forged"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            );

            assert!(context.recheck_source_file(file).is_err(), "case {poison}");

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().clone(),
                ),
                before,
                "case {poison}",
            );
        }
    }

    #[test]
    fn optional_declared_constructor_parameters_preserve_zero_minimum_and_warm_identity() {
        for (source, has_argument) in [
            (
                concat!(
                    "interface Factory { new(value?: any): string; } ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                false,
            ),
            (
                concat!(
                    "interface Factory { ",
                    "(): number; ",
                    "new(value?: any): string; ",
                    "} ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                false,
            ),
            (
                concat!(
                    "interface Factory { ",
                    "new(value?: any): string; ",
                    "(): any; ",
                    "(value: any): any; ",
                    "readonly prototype: string; ",
                    "} ",
                    "declare const factory: Factory; ",
                    "const result = new factory();",
                ),
                false,
            ),
            (
                concat!(
                    "interface Factory { new(value?: any): string; } ",
                    "declare const factory: Factory; ",
                    "const result = new factory(1);",
                ),
                true,
            ),
            (
                concat!(
                    "declare const factory: { new(value?: any): string }; ",
                    "const result = new factory();",
                ),
                false,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_835);
            let mut context = context(&parsed, file);
            let (annotation, owner) = ambient_constructor(&parsed, file, &context, "factory");
            let (construction, constructor) = variable_new(&parsed, file, "result");

            context.check_source_file(file).unwrap();

            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let value = store
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let record = store.signature(signature).unwrap();
            assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
            assert_eq!(record.parameters().len(), 1);
            assert_eq!(record.min_argument_count(), 0);
            assert_eq!(record.resolved_return_type(), Some(bootstrap.string_type));
            assert_eq!(
                store.callable_signature_parameter_types(signature),
                Some([bootstrap.any_type].as_slice()),
            );
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
            );
            assert_eq!(
                store
                    .type_node_links(construction)
                    .and_then(|links| links.resolved_type),
                Some(bootstrap.string_type),
            );
            assert!(matches!(
                validate_stored_callable_set(store, value),
                StoredCallableSetValidation::Valid {
                    family: CallableFamily::DeclaredCallSignatures,
                    projection,
                    ..
                } if projection.construct_signatures.as_ref() == [signature].as_slice()
            ));
            assert!(context.diagnostics().is_empty(), "{source}");
            if has_argument {
                let NodeData::NewExpression(expression) =
                    &parsed.arena.get(construction.node).unwrap().data
                else {
                    panic!("the constructor fixture must retain its new expression")
                };
                let argument = NodeRef::new(
                    construction.arena,
                    construction.file,
                    expression.arguments.as_ref().unwrap().nodes[0],
                );
                assert!(store.type_node_links(argument).is_some());
            }
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn incompatible_declared_constructor_arguments_do_not_publish_values() {
        for source in [
            concat!(
                "declare const factory: { new(value: number): string }; ",
                "const result = new factory(\"wrong\");",
            ),
            concat!(
                "declare const factory: { new(value: number): string }; ",
                "const result = new factory();",
            ),
            "declare const factory: { new(): string }; const result = new factory(1);",
            concat!(
                "declare const factory: abstract new () => string; ",
                "const result = new factory();",
            ),
            concat!(
                "declare const factory: { new(): string } | null; ",
                "const result = new factory();",
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_811);
            let mut context = context(&parsed, file);
            let (annotation, owner) = ambient_constructor(&parsed, file, &context, "factory");
            let (construction, _) = variable_new(&parsed, file, "result");
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    context.check_source_file(file),
                    Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                        _
                    )))
                ),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "{source}",
            );
            assert!(context.store().type_node_links(annotation).is_none());
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn abstract_declared_construct_signature_is_rejected_without_new_publication() {
        let parsed = parse_source_file(
            "declare const factory: { new(): string }; const result = new factory();",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_812);
        let mut context = context(&parsed, file);
        let (annotation, owner) = ambient_constructor(&parsed, file, &context, "factory");
        let (construction, constructor) = variable_new(&parsed, file, "result");
        let value = context.get_type_from_type_node(annotation).unwrap();
        let signature = context
            .store()
            .type_payload(value)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first())
            .copied()
            .unwrap();
        assert!(context.store_mut_for_test().set_signature_flags(
            signature,
            SignatureFlags::CONSTRUCT | SignatureFlags::ABSTRACT,
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(constructor)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().type_node_links(construction).is_none());
        assert!(context.store().symbol_node_links(constructor).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn constructor_arguments_prepare_cold_bootstrap_literals() {
        for (annotation, argument) in [
            ("string", "\"\""),
            ("string", "\"string\""),
            ("number", "0"),
        ] {
            let source = format!(
                "class Model {{ constructor(value: {annotation}) {{}} }} const model = new Model({argument});"
            );
            let parsed = parse_source_file(&source);
            let file = FileId::new(1_808);
            let mut context = context(&parsed, file);
            let (construction, _) = variable_new(&parsed, file, "model");
            let argument = constructor_argument(&parsed, construction);
            context.check_source_file(file).unwrap();
            assert!(context.diagnostics().is_empty());
            let fresh = context
                .store()
                .type_node_links(argument)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let TypeData::Literal(literal) = context.store().type_payload(fresh).unwrap().data()
            else {
                panic!("expected the checked argument's literal type")
            };
            assert_eq!(literal.fresh_type, Some(fresh));
            assert_ne!(literal.regular_type, fresh);
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn required_primitive_constructor_argument_publishes_fresh_literal_and_replays_warm() {
        for (source, numeric) in [
            (
                "class Model { constructor(value: string) {} } const model = new Model(\"ready\");",
                false,
            ),
            (
                "class Model { constructor(value: number) {} } const model = new Model(1);",
                true,
            ),
            (
                concat!(
                    "declare function decorate(",
                    "target: any, key: string | symbol | undefined, index: number",
                    "): void; ",
                    "class Model { constructor(@decorate value: string) {} } ",
                    "const model = new Model(\"ready\");",
                ),
                false,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(1_807);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, constructor) = variable_new(&parsed, file, "model");
            let argument = constructor_argument(&parsed, construction);

            context.check_source_file(file).unwrap();

            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let regular = if numeric {
                bootstrap
                    .cached_number_literal_type(ts_jsnum::from_string("1"))
                    .unwrap()
            } else {
                bootstrap.cached_string_literal_type("ready").unwrap()
            };
            let fresh = store.fresh_type_of_literal_type(regular).unwrap();
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let signature_record = store.signature(signature).unwrap();
            let [parameter] = signature_record.parameters() else {
                panic!("the selected constructor has exactly one parameter")
            };
            let expected_parameter = if numeric {
                bootstrap.number_type
            } else {
                bootstrap.string_type
            };
            assert_eq!(signature_record.min_argument_count(), 1);
            assert_eq!(
                store.value_symbol_links(*parameter),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(expected_parameter),
                    ..ValueSymbolLinks::default()
                }),
            );
            assert_eq!(
                store.type_node_links(argument),
                Some(&TypeNodeLinks {
                    resolved_type: Some(fresh),
                    ..TypeNodeLinks::default()
                }),
            );
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
            );
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn defaulted_parameter_property_constructors_accept_omitted_and_supplied_arguments() {
        for (source, numeric, supplied) in [
            (
                concat!(
                    "class Model { constructor(public value: number = 1) {} } ",
                    "const model = new Model();",
                ),
                true,
                false,
            ),
            (
                concat!(
                    "class Model { constructor(public value: number = 1) {} } ",
                    "const model = new Model(2);",
                ),
                true,
                true,
            ),
            (
                concat!(
                    "class Model { constructor(readonly value: string = 'ready') {} } ",
                    "const model = new Model();",
                ),
                false,
                false,
            ),
            (
                concat!(
                    "class Model { constructor(public readonly value: string = 'ready') {} } ",
                    "const model = new Model('done');",
                ),
                false,
                true,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics,
            );
            let file = FileId::new(1_855);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, constructor) = variable_new(&parsed, file, "model");

            context.check_source_file(file).unwrap();

            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let expected = if numeric {
                bootstrap.number_type
            } else {
                bootstrap.string_type
            };
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let signature_record = store.signature(signature).unwrap();
            let [parameter] = signature_record.parameters() else {
                panic!("the defaulted constructor must retain its parameter symbol")
            };
            let parameter = *parameter;
            let property = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("value"))
                .unwrap();
            assert_ne!(parameter, property, "{source}");
            assert_eq!(signature_record.min_argument_count(), 0, "{source}");
            for symbol in [parameter, property] {
                assert_eq!(
                    store.value_symbol_links(symbol),
                    Some(&ValueSymbolLinks {
                        resolved_type: Some(expected),
                        ..ValueSymbolLinks::default()
                    }),
                    "{source}",
                );
            }
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
                "{source}",
            );
            if supplied {
                let argument = constructor_argument(&parsed, construction);
                assert!(store.type_node_links(argument).is_some(), "{source}");
            }
            assert!(context.diagnostics().is_empty(), "{source}");
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn incompatible_constructor_arguments_reject_before_class_publication() {
        for source in [
            "class Model { constructor(value: string) {} } const model = new Model(1);",
            "class Model { constructor(value: number) {} } const model = new Model(\"ready\");",
            "class Model { constructor(value: string) {} } const model = new Model();",
            concat!(
                "class Model { constructor(public value: number = 1) {} } ",
                "const model = new Model(\"wrong\");",
            ),
            "class Model {} const model = new Model(\"ready\");",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(1_808);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, _) = variable_new(&parsed, file, "model");
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                    construction,
                ))),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
        }
    }

    #[test]
    fn unsupported_interface_constructor_arguments_reject_without_partial_class_publication() {
        let parsed = parse_source_file(concat!(
            "interface Options { value: number; } ",
            "class Super { constructor(value: number) {} } ",
            "class Sub extends Super { ",
            "constructor(public options: Options) { super(options.value); } ",
            "} ",
            "const model = new Sub(1);",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_810);
        let mut context = context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Sub");
        let base = class_symbol(&parsed, file, &context, "Super");
        let (construction, _) = variable_new(&parsed, file, "model");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                construction,
            ))),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().declared_type_links(base).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn constructor_expressions_publish_real_signatures_in_top_level_expression_positions() {
        for (index, source) in [
            "class Model {} new Model();",
            "class Model {} let current: Model; current = new Model();",
            "class Model {} const current: Model = new Model();",
            "class Model { value!: number; } const value = new Model().value;",
            "class Model { run(): void {} } new Model().run();",
            concat!(
                "declare const factory: { new(): string }; ",
                "let value: string = ''; value = new factory();",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_820 + u32::try_from(index).unwrap());
            let mut context = context(&parsed, file);

            context.check_source_file(file).unwrap();

            let constructions = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(constructions.len(), 1, "{source}");
            let construction = constructions[0];
            let signature = context
                .store()
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert!(
                context
                    .store()
                    .signature(signature)
                    .is_some_and(|signature| signature.flags().contains(SignatureFlags::CONSTRUCT)),
                "{source}",
            );
            assert!(
                context
                    .store()
                    .type_node_links(construction)
                    .and_then(|links| links.resolved_type)
                    .is_some(),
                "{source}",
            );
            assert!(context.diagnostics().is_empty(), "{source}");
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().clone(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn constructor_assignment_results_retain_exact_target_diagnostics() {
        let parsed = parse_source_file(concat!(
            "declare const factory: { new(): string }; ",
            "let value: number = 0; ",
            "value = new factory();",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_826);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the incompatible constructor assignment must produce one diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'.",
        );
    }

    #[test]
    fn inaccessible_class_constructor_calls_report_exact_source_diagnostics() {
        for (index, (source, javascript, expected_code, name)) in [
            (
                "class Secret { private constructor() {} } new Secret();",
                false,
                2673,
                "Secret",
            ),
            (
                "class Base { protected constructor() {} } new Base();",
                false,
                2674,
                "Base",
            ),
            (
                "class Secret {\n/** @private */ constructor() {} } new Secret();",
                true,
                2673,
                "Secret",
            ),
            (
                "class Base {\n/** @protected */ constructor() {} } new Base();",
                true,
                2674,
                "Base",
            ),
            (
                concat!(
                    "// https://github.com/microsoft/typescript-go/issues/4219\n",
                    "\n",
                    "class C {\n",
                    "  /** @private */\n",
                    "  constructor() {}\n",
                    "}\n",
                    "new C();",
                ),
                true,
                2673,
                "C",
            ),
            (
                concat!(
                    "class Secret {\n",
                    "  /**\n",
                    "   * @private\n",
                    "   */\n",
                    "  constructor() {}\n",
                    "}\n",
                    "new Secret();",
                ),
                true,
                2673,
                "Secret",
            ),
            (
                concat!(
                    "class Base {\n",
                    "  /**\n",
                    "   * @protected\n",
                    "   */\n",
                    "  constructor() {}\n",
                    "}\n",
                    "new Base();",
                ),
                true,
                2674,
                "Base",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = if javascript {
                parse_javascript_source_file(source)
            } else {
                parse_source_file(source)
            };
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(1_827 + u32::try_from(index).unwrap());
            let mut context = if javascript {
                javascript_context(&parsed, file)
            } else {
                context(&parsed, file)
            };

            context.check_source_file(file).unwrap();

            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("{source} must produce one constructor accessibility diagnostic")
            };
            assert_eq!(diagnostic.diagnostic.code(), expected_code, "{source}");
            assert_eq!(
                diagnostic.diagnostic.arguments,
                vec![name.to_owned()],
                "{source}",
            );
            let node = diagnostic.node.unwrap();
            assert_eq!(
                parsed.arena.get(node.node).unwrap().kind,
                SyntaxKind::NewExpression,
                "{source}",
            );
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.diagnostics().clone(),
                ),
                warm,
                "{source}",
            );
        }
    }

    #[test]
    fn poisoned_constructor_argument_rejects_before_class_publication() {
        let parsed = parse_source_file(
            "class Model { constructor(value: string) {} } const model = new Model(\"ready\");",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_809);
        let mut context = context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");
        let (construction, _) = variable_new(&parsed, file, "model");
        let argument = constructor_argument(&parsed, construction);
        let poison = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            argument,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(argument)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
    }

    #[test]
    fn poisoned_later_new_rejects_before_earlier_class_or_link_publication() {
        let parsed = parse_source_file(concat!(
            "class Early { value!: string; }\n",
            "const early = new Early();\n",
            "class Later { value!: string; }\n",
            "const later = new Later();\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_806);
        let mut context = context(&parsed, file);
        let early_class = class_symbol(&parsed, file, &context, "Early");
        let (early_new, early_constructor) = variable_new(&parsed, file, "early");
        let (later_new, _) = variable_new(&parsed, file, "later");
        let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            later_new,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(later_new))
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        assert!(context.store().declared_type_links(early_class).is_none());
        assert!(context.store().value_symbol_links(early_class).is_none());
        assert!(
            context
                .store()
                .symbol_node_links(early_constructor)
                .is_none()
        );
        assert!(context.store().type_node_links(early_constructor).is_none());
        assert!(context.store().signature_links(early_new).is_none());
        assert!(context.store().type_node_links(early_new).is_none());
        assert_eq!(
            context.store().type_node_links(later_new),
            Some(&TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            })
        );
        assert!(context.diagnostics().is_empty());
    }
}
