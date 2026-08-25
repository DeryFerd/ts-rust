//! Exact source integration for admitted class and declared constructions.
//!
//! This is the dependency-closed `new Model()`, `new Model`, and single-literal
//! constructor branch of pinned TypeScript-Go `checkCallExpression`,
//! `getResolvedSignature`, `resolveNewExpression`, and `resolveCall`.
//! An admitted constructor belongs to one preceding local class, an earlier
//! ambient variable, or an authenticated global `Object`, `Array`, or `Date`
//! constructor. Global arrays retain their real length and generic-item
//! overloads. Planning proves syntax, resolver routes, provider provenance, and
//! cold/warm caches before source execution may publish class or expression
//! state.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_jsnum::Number;

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, ClassError, DeclaredTypeError,
    DeclaredTypeHost, ResolvedSignatureState, SignatureId, SignatureLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    bootstrap::LiteralTypeCacheError,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::CallableFamily,
    classes::{
        ClassConstructorVisibility, ClassMemberPlan, ClassMemberQueryPlan,
        execute_nongeneric_class_member_query, plan_nongeneric_class_member_query,
        preflight_nongeneric_class_member_query,
    },
    declared::{execute_type_parameter, preflight_class_or_interface_reference},
    jsdoc::leading_jsdoc_comment,
    object_members::{PropertyObjectPlan, plan_interface, plan_type_literal},
    signatures::SignatureFlags,
    store::CachedSignatureLookup,
    type_nodes::normalize_numeric_separators,
    type_records::type_list_key,
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

/// Opaque syntax, resolver, and provider proof for one direct construction.
#[derive(Clone, Debug)]
pub(super) struct SourceDefaultNewPlan {
    node: NodeRef,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    target: SourceNewTarget,
    argument: Option<SourceNewArgument>,
    additional_arguments: Vec<SourceNewArgument>,
    parameter: Option<SourceNewParameter>,
}

#[derive(Clone, Debug)]
enum SourceNewTarget {
    Class(Box<ClassMemberQueryPlan>),
    Declared(SourceDeclaredConstructorPlan),
    GlobalObject(SourceGlobalObjectConstructorPlan),
    GlobalArray(SourceGlobalArrayConstructorPlan),
    GlobalDate(SourceGlobalDateConstructorPlan),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceDeclaredConstructorPlan {
    annotation: NodeRef,
    declaration: NodeRef,
    parameter: Option<SourceNewParameter>,
    signature_parameter: Option<SourceNewParameter>,
    min_argument_count: usize,
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

#[derive(Clone, Debug)]
enum SourceNewArgumentValue {
    String(String),
    Number(Number),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNewParameter {
    symbol: SemanticSymbolId,
    type_: TypeId,
}

impl SourceDefaultNewPlan {
    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn constructor(&self) -> NodeRef {
        self.constructor
    }

    pub(super) const fn resolved_symbol(&self) -> SemanticSymbolId {
        self.resolved_symbol
    }

    fn arguments(&self) -> impl Iterator<Item = &SourceNewArgument> {
        self.argument.iter().chain(&self.additional_arguments)
    }

    /// Returns the exact access diagnostic for an authenticated class constructor.
    pub(super) fn constructor_accessibility_diagnostic(
        &self,
        arena: &NodeArena,
        bound: &BoundFile,
        store: &CanonicalTypeMapperStore,
    ) -> Result<Option<(u32, String)>, SourceNewError> {
        let SourceNewTarget::Class(class) = &self.target else {
            return Ok(None);
        };
        let code = match class.constructor_visibility() {
            ClassConstructorVisibility::Private => Some(2673),
            ClassConstructorVisibility::Protected => Some(2674),
            ClassConstructorVisibility::Public => {
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
        let name = store
            .symbol(self.resolved_symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            .filter(|name| !name.is_empty())
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(self.resolved_symbol)))?;
        Ok(Some((code, name.to_owned())))
    }
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
    node: NodeRef,
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
    let argument_start = match new_expression.arguments.as_ref() {
        Some(argument_nodes) => {
            if argument_nodes.has_trailing_comma
                || argument_nodes.range.start < record.range.start
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
                    _ => return Err(unsupported(SourceNewUnsupported::Arguments(node))),
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
    let symbol = store
        .get_merged_symbol(resolved_symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(resolved_symbol)))?;
    if symbol != resolved_symbol {
        return Err(invariant(SourceNewInvariant::MergedSymbol {
            source: resolved_symbol,
            target: symbol,
        }));
    }
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(symbol)))?;
    if symbol_record.check_flags() != CheckFlags::NONE {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }));
    }
    let global_object = identifier.text == "Object"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Object"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    let global_array = identifier.text == "Array"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    let global_date = identifier.text == "Date"
        && store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Date"))
            .and_then(|global| store.get_merged_symbol(global))
            == Some(symbol);
    if !global_array && (arguments.len() > 1 || new_expression.type_arguments.is_some()) {
        return Err(unsupported(if new_expression.type_arguments.is_some() {
            SourceNewUnsupported::TypeArguments(node)
        } else {
            SourceNewUnsupported::Arguments(node)
        }));
    }
    let argument = arguments.first().cloned();
    let additional_arguments = arguments.into_iter().skip(1).collect::<Vec<_>>();
    let (target, parameter) = if global_object {
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
        let parameter = constructor_parameter(store, host, &class)?;
        if argument.is_some() && class.direct_plan().is_none() {
            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
        }
        (SourceNewTarget::Class(Box::new(class)), parameter)
    } else if matches!(
        symbol_record.flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
    ) {
        let declared = plan_declared_constructor(
            arena,
            bound,
            store,
            host,
            node,
            constructor,
            symbol,
            argument.as_ref(),
        )?;
        (SourceNewTarget::Declared(declared), declared.parameter)
    } else {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }));
    };
    if argument.is_some() != parameter.is_some()
        || argument
            .as_ref()
            .zip(parameter)
            .is_some_and(|(argument, parameter)| {
                !argument_matches_parameter(store, argument, parameter)
            })
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }

    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        target,
        argument,
        additional_arguments,
        parameter,
    };
    preflight_default_new_cache(store, &plan)?;
    Ok(plan)
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
    let owner = globals
        .get_source("ObjectConstructor")
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
        || object.name().as_utf8() != Some("Object")
        || object.parent().is_some()
        || object.exports().is_some()
        || object.export_symbol().is_some()
        || globals
            .get_source("Object")
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
        || annotation_identifier.text != "ObjectConstructor"
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("ObjectConstructor")
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
            || return_identifier.text != "Object"
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
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("DateConstructor")
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

    if let Some(date_type) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    {
        let record = store.type_payload(date_type).ok_or_else(reject)?;
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
        {
            return Err(reject());
        }
    }

    for &signature_declaration in signature_declarations {
        let Some(record) = host.node(signature_declaration) else {
            continue;
        };
        let NodeData::ConstructSignatureDeclaration(signature) = &record.data else {
            continue;
        };
        let Some(return_annotation) = signature.type_ else {
            continue;
        };
        let return_annotation = NodeRef::new(
            signature_declaration.arena,
            signature_declaration.file,
            return_annotation,
        );
        let Some(return_record) = host.node(return_annotation) else {
            continue;
        };
        let NodeData::TypeReferenceNode(return_reference) = &return_record.data else {
            continue;
        };
        let return_name = NodeRef::new(
            return_annotation.arena,
            return_annotation.file,
            return_reference.type_name,
        );
        let Some(return_name_record) = host.node(return_name) else {
            continue;
        };
        let NodeData::Identifier(return_identifier) = &return_name_record.data else {
            continue;
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
            continue;
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
            };
            let element = explicit.unwrap_or(inferred);
            if std::iter::once(argument)
                .chain(additional_arguments)
                .any(|argument| {
                    let actual = match &argument.value {
                        SourceNewArgumentValue::String(_) => bootstrap.string_type,
                        SourceNewArgumentValue::Number(_) => bootstrap.number_type,
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
    if object.call_signatures.is_empty()
        || !object.properties.is_empty()
        || !object.methods.is_empty()
        || !object.spreads.is_empty()
        || !object.indexes.is_empty()
        || object.heritage.is_some()
        || object.call_signatures.iter().any(|signature| {
            host.node(signature.declaration)
                .is_none_or(|record| record.kind != SyntaxKind::ConstructSignature)
        })
    {
        return Err(reject());
    }

    for signature in object.call_signatures {
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
        _ => return Err(invalid()),
    };
    let parameter_record = host.node(parameter).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let type_node = parameter_data
        .type_
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
        .ok_or_else(invalid)?;
    let type_record = host.node(type_node).ok_or_else(invalid)?;
    let raw = host
        .bound_file(parameter)
        .and_then(|bound| bound.symbol(parameter))
        .ok_or_else(invalid)?;
    let symbol = store.get_merged_symbol(raw).ok_or_else(invalid)?;
    let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let type_ = match type_record.kind {
        SyntaxKind::StringKeyword => bootstrap.string_type,
        SyntaxKind::NumberKeyword => bootstrap.number_type,
        _ => return Err(invalid()),
    };
    if constructor.kind != SyntaxKind::Constructor
        || parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(declaration.node)
        || type_record.parent != Some(parameter.node)
        || !matches!(type_record.data, NodeData::KeywordTypeNode(_))
        || raw != symbol
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.declarations() != Some(&[parameter])
        || symbol_record.value_declaration() != Some(parameter)
    {
        return Err(invalid());
    }
    Ok(Some(SourceNewParameter { symbol, type_ }))
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
    match &plan.target {
        SourceNewTarget::Class(class) => {
            preflight_nongeneric_class_member_query(store, host, class)?;
            if constructor_parameter(store, host, class)? != plan.parameter {
                return Err(invariant(SourceNewInvariant::InvalidClassPlan(
                    class.declaration(),
                )));
            }
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
    }
    preflight_default_new_cache(store, plan)
}

/// Revalidates every retained construction before reserving any sparse link
/// capacity, then installs only empty default slots. No class execution may
/// begin until this whole-file phase succeeds for every plan.
pub(super) fn prepare_direct_default_news(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
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
        preflight_direct_default_new(store, host, plan)?;
    }

    for plan in plans {
        match &plan.target {
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
    }
    Ok(())
}

/// Publishes the bound Object constructor without resolving unrelated members.
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
    let object_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let parameter = exact_class_value_type(store, global.parameter.symbol)?;
    let signature = exact_signature_cache(store, global.declaration).map_err(|()| invalid())?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if signature.is_some()
        || annotation.is_some_and(|type_| Some(type_) != declared)
        || object_value.is_some_and(|type_| Some(type_) != declared)
        || parameter.is_some_and(|type_| type_ != global.parameter.type_)
        || return_annotation.is_some_and(|type_| type_ != global.object_type)
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
    let missing_value_symbols =
        usize::from(store.value_symbol_links(plan.resolved_symbol).is_none())
            + usize::from(store.value_symbol_links(global.parameter.symbol).is_none());
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(global.declaration).is_none(),
        ))
        || !store.try_reserve_type_node_links(missing_type_nodes)
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
        .expect("the authenticated Object constructor reserved its bound signature");
    assert!(store.set_type_node_links(
        global.annotation,
        TypeNodeLinks {
            resolved_type: Some(value_type),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_type_node_links(
        global.return_annotation,
        TypeNodeLinks {
            resolved_type: Some(global.object_type),
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
    let date_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let signature = exact_signature_cache(store, global.declaration).map_err(|()| invalid())?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if signature.is_some()
        || annotation.is_some_and(|type_| Some(type_) != declared)
        || date_value.is_some_and(|type_| Some(type_) != declared)
        || return_annotation.is_some_and(|type_| Some(type_) != date_type)
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
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(global.declaration).is_none(),
        ))
        || !store.try_reserve_type_node_links(missing_type_nodes)
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
    assert!(store.set_type_node_links(
        global.return_annotation,
        TypeNodeLinks {
            resolved_type: Some(instance_type),
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
    preflight_direct_default_new(store, host, plan)?;
    preflight_prepared_default_new_cache(store, plan)?;
    let selected = match &plan.target {
        SourceNewTarget::Class(class) => {
            let members = execute_nongeneric_class_member_query(store, host, class)?;
            let selected = CheckedSourceDefaultNew {
                value_type: members.shells().value_type(),
                instance_type: members.shells().instance_type(),
                signature: members.default_construct_signature(),
            };
            validate_selected_default_signature(
                store,
                plan,
                class,
                selected.value_type,
                selected.instance_type,
                selected.signature,
            )?;
            selected
        }
        SourceNewTarget::Declared(declared) => {
            resolved_declared_constructor(store, plan, declared)?.ok_or_else(|| {
                invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                ))
            })?
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
    };
    let CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    } = selected;
    let argument_types = plan
        .arguments()
        .map(|argument| {
            let regular = match &argument.value {
                SourceNewArgumentValue::String(value) => {
                    store.regular_string_literal_type(value.clone())
                }
                SourceNewArgumentValue::Number(value) => store.regular_number_literal_type(*value),
            }
            .map_err(|error| literal_cache_error(argument.node, error))?;
            store
                .fresh_type_of_literal_type(regular)
                .map_err(|error| literal_cache_error(argument.node, error))
        })
        .collect::<Result<Vec<_>, _>>()?;
    preflight_publication_cache(
        store,
        plan,
        value_type,
        instance_type,
        signature,
        &argument_types,
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
    assert!(store.set_symbol_node_links(plan.constructor, symbol_links));
    assert!(store.set_type_node_links(plan.constructor, constructor_links));
    assert!(store.set_signature_links(plan.node, signature_links));
    assert!(store.set_type_node_links(plan.node, expression_links));
    for (argument, argument_type) in plan.arguments().zip(argument_types) {
        assert!(store.set_type_node_links(
            argument.node,
            TypeNodeLinks {
                resolved_type: Some(argument_type),
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

fn preflight_prepared_default_new_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    if store.symbol_node_links(plan.constructor).is_none()
        || store.type_node_links(plan.constructor).is_none()
        || store.signature_links(plan.node).is_none()
        || store.type_node_links(plan.node).is_none()
        || plan
            .arguments()
            .any(|argument| store.type_node_links(argument.node).is_none())
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    preflight_default_new_cache(store, plan)
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
    if projection.owner != value_type
        || !projection.call_signatures.is_empty()
        || projection.construct_signatures.is_empty()
    {
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
            .declared_type_links(plan.resolved_symbol)
            .and_then(|links| links.declared_type)
            != Some(global.object_type)
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }

    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type: global.object_type,
        signature,
    }))
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
    let date_value = exact_class_value_type(store, plan.resolved_symbol)?;
    let return_annotation =
        exact_type_cache(store, global.return_annotation).map_err(|()| invalid())?;
    if annotation.is_some_and(|type_| Some(type_) != value_type)
        || date_value.is_some_and(|type_| Some(type_) != value_type)
        || return_annotation.is_some_and(|type_| Some(type_) != instance_type)
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

fn preflight_default_new_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
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

    match &plan.target {
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
                    store, plan, class, value, instance, signature,
                )?;
            } else if signature.is_some() {
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
    }
    Ok(())
}

fn preflight_publication_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
    argument_types: &[TypeId],
) -> Result<(), SourceNewError> {
    preflight_prepared_default_new_cache(store, plan)?;
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
    if plan.arguments().count() != argument_types.len() {
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
    };
    regular
        .map(|regular| {
            store
                .fresh_type_of_literal_type(regular)
                .map_err(|error| literal_cache_error(argument.node, error))
        })
        .transpose()
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
    plan: &SourceDefaultNewPlan,
    class: &ClassMemberQueryPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
) -> Result<(), SourceNewError> {
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
    if signature_record.flags() != SignatureFlags::CONSTRUCT
        || signature_record
            .flags()
            .intersects(SignatureFlags::ABSTRACT)
        || signature_record.declaration() != class.constructor_declaration()
        || !signature_record.type_parameters().is_empty()
        || signature_record.parameters()
            != plan.parameter.map(|parameter| parameter.symbol).as_slice()
        || signature_record.this_parameter().is_some()
        || signature_record.min_argument_count() != i32::from(plan.parameter.is_some())
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
    if let Some(parameter) = plan.parameter
        && store.value_symbol_links(parameter.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(parameter.type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    let TypeData::Interface(instance) = store
        .type_payload(instance_type)
        .map(super::type_records::TypeRecord::data)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(class.symbol())))?
    else {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            class.symbol(),
        )));
    };
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
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks, SourceCheckError,
        UnsupportedSourceSyntax,
    };

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
            .and_then(|owner| owner.members())
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
    fn incompatible_constructor_arguments_reject_before_class_publication() {
        for source in [
            "class Model { constructor(value: string) {} } const model = new Model(1);",
            "class Model { constructor(value: number) {} } const model = new Model(\"ready\");",
            "class Model { constructor(value: string) {} } const model = new Model();",
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
                "class Secret { /** @private */ constructor() {} } new Secret();",
                true,
                2673,
                "Secret",
            ),
            (
                "class Base { /** @protected */ constructor() {} } new Base();",
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
