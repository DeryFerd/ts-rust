use std::collections::{BTreeMap, HashMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    SemanticSymbolId, SymbolFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    SignatureId, TypeId, TypeResolutionTarget, TypeSystemPropertyName, UnsupportedDeclaredTypeKind,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    declared::{
        cached_ordinary_type_parameter_owner, execute_type_parameter,
        explicit_type_parameter_symbols, get_declared_class_interface_or_type_parameter,
        malformed_alias_merge, preflight_class_or_interface_reference, preflight_node,
        preflight_type_parameter_symbol, type_list_key,
    },
    functions::{
        self, FunctionTypeError, FunctionTypePlan, PendingFunctionTypeProof, PendingParameterTypes,
    },
    global_types::{
        create_type_from_generic_global_type, preflight_generic_global_type_target,
        validate_generic_global_type_instantiation,
    },
    object_members::{self, PropertyObjectError, PropertyObjectPlan, PropertyObjectState},
    signatures::Signature,
    source_callables::{
        self, PendingSourceCallableParameterTypes, SourceCallableError, SourceCallableFamily,
    },
    type_records::{CacheHashKey, TypeData, TypeRecord},
    types::ObjectFlags,
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct CanonicalTypeQueryOptions {
    pub strict_builtin_iterator_return: bool,
}

impl From<CanonicalCheckerOptions> for CanonicalTypeQueryOptions {
    fn from(options: CanonicalCheckerOptions) -> Self {
        Self {
            strict_builtin_iterator_return: options.strict_builtin_iterator_return,
        }
    }
}

impl From<&CanonicalCheckerOptions> for CanonicalTypeQueryOptions {
    fn from(options: &CanonicalCheckerOptions) -> Self {
        (*options).into()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeNodeUnavailable {
    UnsupportedSyntax {
        node: NodeRef,
        kind: SyntaxKind,
    },
    JsDoc(NodeRef),
    InvalidParenthesizedType(NodeRef),
    InvalidTypeReference(NodeRef),
    QualifiedTypeReference(NodeRef),
    TypeArgumentsUnsupported(NodeRef),
    MissingTypeReference(NodeRef),
    ImportAliasTypeReference {
        node: NodeRef,
        alias: SemanticSymbolId,
    },
    UnsupportedReferenceTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    GenericReferenceUnsupported {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    GenericAliasConstraintUnsupported {
        alias: SemanticSymbolId,
        parameter: NodeRef,
    },
    GenericAliasInstantiationUnsupported {
        alias: SemanticSymbolId,
        declared_type: TypeId,
    },
    MissingGenericAliasMetadata(SemanticSymbolId),
    InvalidGenericAliasInstantiationCache(SemanticSymbolId),
    GenericAliasDefaultReferenceUnsupported {
        alias: SemanticSymbolId,
        default_type: NodeRef,
        referenced_parameter: SemanticSymbolId,
    },
    CircularGenericAliasDefault {
        alias: SemanticSymbolId,
        default_type: NodeRef,
    },
    InvalidTypeAliasSymbol(SemanticSymbolId),
    MissingTypeAliasDeclaration(SemanticSymbolId),
    InvalidTypeAliasDeclaration(NodeRef),
    JsDocTypeAlias(NodeRef),
    InvalidCachedTypeAlias(SemanticSymbolId),
    InvalidCachedSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    CheckerOptionMismatch {
        established_strict_builtin_iterator_return: bool,
        requested_strict_builtin_iterator_return: bool,
    },
    DiagnosticOwnerRequired(SemanticSymbolId),
    MissingPlannedTypeAlias(SemanticSymbolId),
    MissingPlannedTypeReference(NodeRef),
    InvalidLiteralType(NodeRef),
    MissingPlannedLiteralType(NodeRef),
    InvalidLiteralCacheValue,
    InvalidCachedLiteralType(TypeId),
    InvalidUnionType(NodeRef),
    MissingPlannedUnionType(NodeRef),
    UnsupportedUnionConstituent(NodeRef),
    UnsupportedUnionConstituentType(TypeId),
    InvalidCachedUnionType(TypeId),
    InvalidCachedArrayType(TypeId),
    InvalidFunctionType(NodeRef),
    InvalidFunctionSignature(SignatureId),
    InvalidUnionAlias(SemanticSymbolId),
    InvalidPreparedTypeQuery,
    LiteralTypeCapacity,
    ResolutionStackInvariant(SemanticSymbolId),
}

#[derive(Clone, Debug)]
struct TypeAliasPlan {
    name: NodeRef,
    name_text: String,
    type_node: NodeRef,
    type_parameters: Vec<PlannedTypeParameter>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedTypeParameter {
    symbol: SemanticSymbolId,
    default_type: Option<NodeRef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PlannedTypeReference {
    symbol: SemanticSymbolId,
    type_arguments: Vec<NodeRef>,
    alias_owner: Option<SemanticSymbolId>,
    arity: PlannedTypeReferenceArity,
    global_array_target: Option<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PlannedTypeReferenceArity {
    Valid,
    NotGeneric,
    InvalidGeneric { minimum: usize, maximum: usize },
}

#[derive(Clone, Debug, PartialEq)]
enum PlannedLiteralType {
    Null,
    String(String),
    Number {
        value: Number,
        unary_operand: Option<Number>,
    },
    BigInt {
        value: PseudoBigInt,
        unary_operand: Option<PseudoBigInt>,
    },
    Boolean(bool),
}

#[derive(Debug, Default)]
struct TypeQueryPlan {
    arrays: BTreeMap<NodeRef, PlannedArrayType>,
    aliases: BTreeMap<SemanticSymbolId, TypeAliasPlan>,
    references: BTreeMap<NodeRef, PlannedTypeReference>,
    literals: BTreeMap<NodeRef, PlannedLiteralType>,
    unions: BTreeMap<NodeRef, PlannedUnionType>,
    type_literals: BTreeMap<NodeRef, PropertyObjectPlan>,
    interfaces: BTreeMap<SemanticSymbolId, PropertyObjectPlan>,
    functions: BTreeMap<NodeRef, FunctionTypePlan>,
    pending_function_proofs: Vec<PendingFunctionTypeProof>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedArrayType {
    element_type: NodeRef,
    fallback: Option<TypeId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PlannedUnionType {
    types: Vec<NodeRef>,
    alias_symbol: Option<SemanticSymbolId>,
}

#[derive(Clone, Copy, Debug)]
struct CachedTypeAlias {
    declared_type: TypeId,
    type_parameter_count: usize,
    missing_generic_metadata: bool,
}

fn type_alias_instantiation_cache_key(
    type_arguments: &[TypeId],
    alias: Option<(u64, &[TypeId])>,
) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    write_type_list(&mut hasher, type_arguments);
    if let Some((symbol, arguments)) = alias {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_type_list(&mut hasher, arguments);
    } else {
        hasher.update(&[0]);
    }
    CacheHashKey::new(hasher.digest128())
}

fn write_type_list(hasher: &mut Xxh3, types: &[TypeId]) {
    hasher.update(
        &u64::try_from(types.len())
            .expect("type-list length must fit the pinned uint64 encoding")
            .to_le_bytes(),
    );
    for type_ in types {
        hasher.update(&type_.get().to_le_bytes());
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CachedTypeAliasRhs {
    DirectUnion,
    TypeReference(NodeRef),
    TypeLiteral(NodeRef),
    FunctionType(NodeRef),
    NonUnion,
}

fn type_node_unavailable(reason: TypeNodeUnavailable) -> DeclaredTypeError {
    DeclaredTypeError::TypeNodeUnavailable(reason)
}

fn property_object_error(error: PropertyObjectError) -> DeclaredTypeError {
    match error {
        PropertyObjectError::InvalidTypeLiteral(node)
        | PropertyObjectError::InvalidObjectLiteral(node)
        | PropertyObjectError::InvalidCachedTypeLiteral { node, .. } => {
            type_node_unavailable(TypeNodeUnavailable::InvalidLiteralType(node))
        }
        PropertyObjectError::InvalidInterface { declaration, .. } => {
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::InvalidInterfaceDeclaration(
                declaration,
            ))
        }
        PropertyObjectError::InvalidInterfaceSymbol(symbol) => {
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::MissingDeclarations(symbol))
        }
        PropertyObjectError::UnsupportedMember { node, kind } => {
            type_node_unavailable(TypeNodeUnavailable::UnsupportedSyntax { node, kind })
        }
        PropertyObjectError::InvalidCachedInterface { symbol, type_ } => {
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                symbol,
                declared_type: type_,
            })
        }
        PropertyObjectError::Capacity(_) => {
            type_node_unavailable(TypeNodeUnavailable::LiteralTypeCapacity)
        }
    }
}

fn function_type_error(error: FunctionTypeError) -> DeclaredTypeError {
    match error {
        FunctionTypeError::DeclaredType(error) => error,
        FunctionTypeError::LiteralCache(error) => type_construction_error(error),
        error @ (FunctionTypeError::Unsupported(_) | FunctionTypeError::Invariant(_)) => {
            let node = error
                .node()
                .expect("syntax and invariant function errors retain their node");
            type_node_unavailable(match error {
                FunctionTypeError::Unsupported(_) => TypeNodeUnavailable::UnsupportedSyntax {
                    node,
                    kind: SyntaxKind::FunctionType,
                },
                FunctionTypeError::Invariant(_) => TypeNodeUnavailable::InvalidFunctionType(node),
                FunctionTypeError::DeclaredType(_) | FunctionTypeError::LiteralCache(_) => {
                    unreachable!("covered above")
                }
            })
        }
    }
}

fn function_signature_error(error: FunctionTypeError, signature: SignatureId) -> DeclaredTypeError {
    match error {
        FunctionTypeError::DeclaredType(error) => error,
        FunctionTypeError::LiteralCache(error) => type_construction_error(error),
        FunctionTypeError::Unsupported(_) => function_type_error(error),
        FunctionTypeError::Invariant(_) => {
            type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
        }
    }
}

fn source_callable_error(
    error: SourceCallableError,
    family: SourceCallableFamily,
) -> DeclaredTypeError {
    match error {
        SourceCallableError::DeclaredType(error) => error,
        SourceCallableError::LiteralCache(error) => type_construction_error(error),
        error @ SourceCallableError::Unsupported(_) => {
            let node = error
                .node()
                .expect("unsupported source-callable errors retain their node");
            type_node_unavailable(TypeNodeUnavailable::UnsupportedSyntax {
                node,
                kind: family.syntax_kind(),
            })
        }
        error @ SourceCallableError::Invariant(_) => {
            let node = error
                .node()
                .expect("source-callable invariants retain their node");
            type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(node))
        }
    }
}

fn source_callable_signature_error(
    error: SourceCallableError,
    family: SourceCallableFamily,
    signature: SignatureId,
) -> DeclaredTypeError {
    match error {
        SourceCallableError::DeclaredType(error) => error,
        SourceCallableError::LiteralCache(error) => type_construction_error(error),
        SourceCallableError::Unsupported(_) => source_callable_error(error, family),
        SourceCallableError::Invariant(_) => {
            type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
        }
    }
}

fn generic_global_instantiation_argument(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<TypeId> {
    let arguments = match store.type_payload(type_)?.data() {
        TypeData::TypeReference(reference) => reference.resolved_type_arguments.as_deref(),
        TypeData::Interface(interface) => interface.reference.resolved_type_arguments.as_deref(),
        _ => None,
    }?;
    let [argument] = arguments else {
        return None;
    };
    Some(*argument)
}

fn type_construction_error(error: LiteralTypeCacheError) -> DeclaredTypeError {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
        ),
        LiteralTypeCacheError::InvalidValue => {
            type_node_unavailable(TypeNodeUnavailable::InvalidLiteralCacheValue)
        }
        LiteralTypeCacheError::InvalidCachedLiteral(literal) => {
            type_node_unavailable(TypeNodeUnavailable::InvalidCachedLiteralType(literal))
        }
        LiteralTypeCacheError::InvalidCachedUnion(union) => {
            type_node_unavailable(TypeNodeUnavailable::InvalidCachedUnionType(union))
        }
        LiteralTypeCacheError::UnsupportedUnionConstituent(type_) => {
            type_node_unavailable(TypeNodeUnavailable::UnsupportedUnionConstituentType(type_))
        }
        LiteralTypeCacheError::ArrayType { type_, .. } => {
            type_node_unavailable(TypeNodeUnavailable::InvalidCachedArrayType(type_))
        }
        LiteralTypeCacheError::InvalidUnionAlias(symbol) => {
            type_node_unavailable(TypeNodeUnavailable::InvalidUnionAlias(symbol))
        }
        LiteralTypeCacheError::InvalidPreparedQuery => {
            type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery)
        }
        LiteralTypeCacheError::Capacity => {
            type_node_unavailable(TypeNodeUnavailable::LiteralTypeCapacity)
        }
    }
}

pub(super) fn normalize_numeric_separators(text: &str) -> Option<String> {
    if text.is_empty() || text.starts_with(['+', '-']) || text.ends_with('n') {
        return None;
    }
    let radix = numeric_radix(text);
    if !valid_numeric_separators(text, radix) {
        return None;
    }
    let normalized = text.replace('_', "");
    normalized
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_digit() || first == '.')
        .then_some(normalized)
}

pub(super) fn normalize_bigint_literal(text: &str) -> Option<String> {
    let body = text.strip_suffix('n')?;
    if body.is_empty() || body.starts_with(['+', '-']) {
        return None;
    }
    let radix = numeric_radix(body);
    if !valid_numeric_separators(body, radix) {
        return None;
    }
    let normalized = body.replace('_', "");
    let digits = match radix {
        2 | 8 | 16 => normalized.get(2..)?,
        _ => normalized.as_str(),
    };
    if digits.is_empty()
        || !digits.chars().all(|digit| match radix {
            2 => matches!(digit, '0' | '1'),
            8 => matches!(digit, '0'..='7'),
            16 => digit.is_ascii_hexdigit(),
            _ => digit.is_ascii_digit(),
        })
    {
        return None;
    }
    Some(format!("{normalized}n"))
}

fn numeric_radix(text: &str) -> u32 {
    match text.get(..2) {
        Some("0b" | "0B") => 2,
        Some("0o" | "0O") => 8,
        Some("0x" | "0X") => 16,
        _ => 10,
    }
}

fn valid_numeric_separators(text: &str, radix: u32) -> bool {
    let bytes = text.as_bytes();
    bytes.iter().enumerate().all(|(index, byte)| {
        if *byte != b'_' {
            return true;
        }
        let valid_digit = |candidate: u8| match radix {
            2 => matches!(candidate, b'0' | b'1'),
            8 => matches!(candidate, b'0'..=b'7'),
            16 => candidate.is_ascii_hexdigit(),
            _ => candidate.is_ascii_digit(),
        };
        index
            .checked_sub(1)
            .and_then(|previous| bytes.get(previous))
            .copied()
            .is_some_and(valid_digit)
            && bytes.get(index + 1).copied().is_some_and(valid_digit)
    })
}

fn symbol_is_builtin_iterator_return(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> bool {
    store
        .symbol(symbol)
        .and_then(|record| record.name().as_utf8())
        == Some("BuiltinIteratorReturn")
}

fn valid_type_alias_identity_seed(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
    identity_seed: TypeId,
    strict_builtin_iterator_return: bool,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return identity_seed == declared_type;
    };
    if symbol_is_builtin_iterator_return(store, symbol)
        && identity_seed == bootstrap.intrinsic_marker_type
    {
        let expected = if strict_builtin_iterator_return {
            bootstrap.undefined_type
        } else {
            bootstrap.any_type
        };
        declared_type == expected
    } else {
        identity_seed == declared_type
    }
}

fn cached_type_alias(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    strict_builtin_iterator_return: bool,
) -> Result<Option<CachedTypeAlias>, DeclaredTypeError> {
    let Some(links) = store.type_alias_links(symbol) else {
        return Ok(None);
    };
    if store
        .symbol(symbol)
        .and_then(|symbol| symbol.declarations())
        .is_none_or(|declarations| declarations.len() != 1)
    {
        return Err(type_node_unavailable(
            TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
        ));
    }
    let Some(declared_type) = links.declared_type else {
        if links.type_parameters.is_some() || links.instantiations.is_some() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        return Ok(None);
    };

    let expected_parameter_symbols = cached_alias_parameter_symbols(store, host, symbol)?;
    let mut missing_generic_metadata = false;
    let type_parameter_count = match links.type_parameters.as_deref() {
        None if links.instantiations.is_none() => {
            if expected_parameter_symbols
                .as_ref()
                .is_some_and(|parameters| !parameters.is_empty())
            {
                let is_error_type = store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| declared_type == bootstrap.error_type);
                if !is_error_type {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
                    ));
                }
                missing_generic_metadata = true;
            }
            0
        }
        Some(type_parameters) if !type_parameters.is_empty() => {
            let unique_parameters = type_parameters.iter().copied().collect::<HashSet<_>>();
            let parameter_symbols = type_parameters
                .iter()
                .map(|parameter| cached_ordinary_type_parameter_owner(store, *parameter))
                .collect::<Option<Vec<_>>>();
            let parameters_are_valid =
                unique_parameters.len() == type_parameters.len() && parameter_symbols.is_some();
            if let Some(expected) = &expected_parameter_symbols
                && parameter_symbols.as_deref() != Some(expected.as_slice())
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
                ));
            }
            let has_identity_seed = links.instantiations.as_ref().is_some_and(|instantiations| {
                instantiations
                    .values()
                    .all(|instantiation| store.type_payload(*instantiation).is_some())
                    && instantiations
                        .get(&type_list_key(type_parameters))
                        .is_some_and(|identity_seed| {
                            valid_type_alias_identity_seed(
                                store,
                                symbol,
                                declared_type,
                                *identity_seed,
                                strict_builtin_iterator_return,
                            )
                        })
            });
            if !parameters_are_valid || !has_identity_seed {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
                ));
            }
            type_parameters.len()
        }
        None | Some(_) => {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
    };
    Ok(Some(CachedTypeAlias {
        declared_type,
        type_parameter_count,
        missing_generic_metadata,
    }))
}

fn cached_alias_parameter_symbols(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<Vec<SemanticSymbolId>>, DeclaredTypeError> {
    let declaration = store
        .symbol(symbol)
        .and_then(|symbol| symbol.declarations())
        .and_then(|declarations| declarations.first())
        .copied()
        .ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol))
        })?;
    if host.source(declaration).is_none() {
        return Ok(None);
    }
    let declaration_node = preflight_node(store, host, declaration)?;
    let NodeData::TypeAliasDeclaration(alias) = &declaration_node.data else {
        return Err(type_node_unavailable(
            TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
        ));
    };
    if declaration_node.kind != SyntaxKind::TypeAliasDeclaration
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(type_node_unavailable(
            TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
        ));
    }
    explicit_type_parameter_symbols(
        store,
        host,
        declaration,
        alias.type_parameters.as_ref(),
        &mut HashSet::new(),
    )
    .map(Some)
}

struct TypeQueryPlanner<'store, 'host, 'arena> {
    store: &'store CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    array_type: Option<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
    strict_builtin_iterator_return: bool,
    plan: TypeQueryPlan,
    planning_defaults: HashSet<(SemanticSymbolId, NodeRef)>,
    planning_interfaces: HashSet<SemanticSymbolId>,
    active_structural_aliases: Vec<(SemanticSymbolId, usize)>,
    function_indirection_depth: usize,
}

impl<'store, 'host, 'arena> TypeQueryPlanner<'store, 'host, 'arena> {
    fn new(
        store: &'store CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        array_type: Option<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
        strict_builtin_iterator_return: bool,
    ) -> Self {
        Self {
            store,
            host,
            array_type,
            array_targets,
            strict_builtin_iterator_return,
            plan: TypeQueryPlan::default(),
            planning_defaults: HashSet::new(),
            planning_interfaces: HashSet::new(),
            active_structural_aliases: Vec::new(),
            function_indirection_depth: 0,
        }
    }

    fn finish(self) -> TypeQueryPlan {
        self.plan
    }

    fn plan_type_node(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        if let Some(alias) = self.direct_type_alias_owner(node)? {
            self.plan_type_alias(alias, false).map(|_| ())
        } else {
            self.plan_type_node_in_context(node, None, false)
        }
    }

    fn direct_type_alias_owner(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, DeclaredTypeError> {
        let mut child = node;
        loop {
            let Some(parent) = preflight_node(self.store, self.host, child)?.parent else {
                return Ok(None);
            };
            let parent = NodeRef::new(node.arena, node.file, parent);
            let record = preflight_node(self.store, self.host, parent)?;
            match &record.data {
                NodeData::ParenthesizedTypeNode(parenthesized)
                    if parenthesized.type_ == child.node =>
                {
                    child = parent;
                }
                NodeData::TypeAliasDeclaration(alias)
                    if record.kind == SyntaxKind::TypeAliasDeclaration
                        && alias.type_ == child.node =>
                {
                    let bound = self.host.bound_file(parent).ok_or({
                        DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::MissingOrForeignFacts(parent),
                        )
                    })?;
                    let symbol = bound
                        .symbol(parent)
                        .and_then(|symbol| self.store.get_merged_symbol(symbol))
                        .ok_or_else(|| {
                            type_node_unavailable(TypeNodeUnavailable::InvalidTypeAliasDeclaration(
                                parent,
                            ))
                        })?;
                    let flags = self
                        .store
                        .symbol(symbol)
                        .map(ts_binder::semantic::Symbol::flags)
                        .ok_or(DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::SymbolNotOwned(symbol),
                        ))?;
                    if !self.host.symbol_matches(self.store, parent, symbol)
                        || !flags.contains(SymbolFlags::TYPE_ALIAS)
                        || malformed_alias_merge(flags)
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidTypeAliasDeclaration(parent),
                        ));
                    }
                    return Ok(Some(symbol));
                }
                _ => return Ok(None),
            }
        }
    }

    fn plan_type_node_in_context(
        &mut self,
        node: NodeRef,
        alias_owner: Option<SemanticSymbolId>,
        union_constituent: bool,
    ) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        if record.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(TypeNodeUnavailable::JsDoc(node)));
        }
        let cached = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        let mut deferred_cached_validation = false;
        if let Some(cached) = cached {
            if record.kind == SyntaxKind::UnionType {
                let derived_alias = self.direct_union_alias(node)?;
                if alias_owner.is_some() && derived_alias != alias_owner {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidUnionType(node),
                    ));
                }
                match self.validate_cached_union_result(cached, alias_owner.or(derived_alias)) {
                    Ok(()) => return Ok(()),
                    Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                        if self.is_pending_stored_function_type(type_) =>
                    {
                        deferred_cached_validation = true;
                    }
                    Err(error) => return Err(type_construction_error(error)),
                }
            } else if union_constituent
                && !matches!(
                    record.kind,
                    SyntaxKind::FunctionType | SyntaxKind::TypeReference
                )
            {
                match self.validate_cached_union_result(cached, None) {
                    Ok(()) => {}
                    Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                        if self.is_pending_stored_function_type(type_) =>
                    {
                        deferred_cached_validation = true;
                    }
                    Err(error) => return Err(type_construction_error(error)),
                }
            }
        }
        let result = match record.kind {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword => Ok(()),
            SyntaxKind::ParenthesizedType => {
                let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                };
                let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
                if preflight_node(self.store, self.host, inner)?.parent != Some(node.node) {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                }
                self.plan_type_node_in_context(inner, alias_owner, union_constituent)
            }
            SyntaxKind::LiteralType => self.plan_literal_type(node),
            // Global-aware shorthand `T[]` is the installed array-reference
            // syntax. Direct `Array<T>`/`ReadonlyArray<T>` references still
            // wait on generic interface type-argument instantiation.
            SyntaxKind::ArrayType if union_constituent && self.array_targets.is_none() => Err(
                type_node_unavailable(TypeNodeUnavailable::UnsupportedUnionConstituent(node)),
            ),
            SyntaxKind::TypeLiteral if union_constituent => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(node),
            )),
            SyntaxKind::ArrayType => self.plan_array_type(node, alias_owner),
            SyntaxKind::TypeLiteral => self.plan_property_type_literal(node, alias_owner),
            SyntaxKind::FunctionType => self.plan_function_type(node, alias_owner),
            SyntaxKind::TypeReference => {
                self.plan_type_reference(node, alias_owner, union_constituent)
            }
            SyntaxKind::UnionType => self.plan_union_type(node, alias_owner),
            kind if union_constituent => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(node),
            )),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
        };
        result?;
        if let Some(cached) = cached {
            if deferred_cached_validation && record.kind == SyntaxKind::UnionType {
                let derived_alias = self.direct_union_alias(node)?;
                self.validate_cached_union_result(cached, alias_owner.or(derived_alias))
                    .map_err(type_construction_error)?;
            } else if deferred_cached_validation
                || union_constituent
                    && matches!(
                        record.kind,
                        SyntaxKind::FunctionType | SyntaxKind::TypeReference
                    )
            {
                self.validate_cached_union_result(cached, None)
                    .map_err(type_construction_error)?;
            }
        }
        Ok(())
    }

    fn validate_cached_union_result(
        &self,
        cached: TypeId,
        expected_alias: Option<SemanticSymbolId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.store
            .validate_cached_union_result_with_pending_functions(
                self.array_targets,
                cached,
                expected_alias,
                &self.plan.pending_function_proofs,
            )
    }

    fn validate_cached_array_capability(
        &self,
        cached: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.store
            .validate_cached_array_capability_with_pending_functions(
                self.array_targets,
                cached,
                &self.plan.pending_function_proofs,
            )
    }

    fn is_pending_stored_function_type(&self, type_: TypeId) -> bool {
        functions::validate_stored_function_type(self.store, type_)
            == functions::StoredFunctionTypeValidation::Pending
    }

    fn plan_array_type(
        &mut self,
        node: NodeRef,
        alias_owner: Option<SemanticSymbolId>,
    ) -> Result<(), DeclaredTypeError> {
        let array_type = self.array_type.ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::UnsupportedSyntax {
                node,
                kind: SyntaxKind::ArrayType,
            })
        })?;
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::ArrayTypeNode(array) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        let element_type = NodeRef::new(node.arena, node.file, array.element_type);
        let element_record = preflight_node(self.store, self.host, element_type)?;
        if record.kind != SyntaxKind::ArrayType
            || element_record.parent != Some(node.node)
            || element_record.range.start != record.range.start
            || element_record.range.end >= record.range.end
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        let fallback = preflight_generic_global_type_target(self.store, array_type)
            .map_err(|_| type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)))?;
        let cached = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        if let Some(cached) = cached {
            validate_generic_global_type_instantiation(self.store, array_type, cached).map_err(
                |_| type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)),
            )?;
        }
        // A missing or malformed global Array resolves directly to the empty
        // object fallback before the element type is consulted upstream.
        if fallback.is_none() {
            if let Some(alias) = alias_owner
                && self
                    .plan
                    .aliases
                    .get(&alias)
                    .is_some_and(|plan| !plan.type_parameters.is_empty())
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported {
                        node,
                        symbol: alias,
                    },
                ));
            }
            self.plan_type_node_in_context(element_type, None, false)?;
            if let Some(cached) = cached {
                let TypeData::TypeReference(reference) = self
                    .store
                    .type_payload(cached)
                    .expect("the generic-global cache was preflighted")
                    .data()
                else {
                    unreachable!("an initialized generic-global cache owns references")
                };
                let cached_element = reference
                    .resolved_type_arguments
                    .as_deref()
                    .expect("the generic-global cache was preflighted")[0];
                if self.cached_array_element_identity(element_type)? != Some(cached_element) {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidTypeReference(node),
                    ));
                }
            }
        }
        let planned = PlannedArrayType {
            element_type,
            fallback,
        };
        if let Some(existing) = self.plan.arrays.insert(node, planned)
            && existing != planned
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        Ok(())
    }

    fn cached_array_element_identity(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
            return self.cached_array_element_identity(NodeRef::new(
                node.arena,
                node.file,
                parenthesized.type_,
            ));
        }
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?;
        let keyword = match record.kind {
            SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
            SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
            SyntaxKind::StringKeyword => Some(bootstrap.string_type),
            SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
            SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
            SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
            SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
            SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
            SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
            SyntaxKind::NullKeyword => Some(bootstrap.null_type),
            SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
            SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
            SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
            _ => None,
        };
        Ok(keyword.or_else(|| {
            self.store
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
        }))
    }

    fn plan_property_type_literal(
        &mut self,
        node: NodeRef,
        alias_owner: Option<SemanticSymbolId>,
    ) -> Result<(), DeclaredTypeError> {
        if let Some(alias) = alias_owner
            && self
                .plan
                .aliases
                .get(&alias)
                .is_some_and(|plan| !plan.type_parameters.is_empty())
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::GenericReferenceUnsupported {
                    node,
                    symbol: alias,
                },
            ));
        }
        let planned = object_members::plan_type_literal(self.store, self.host, node, alias_owner)
            .map_err(property_object_error)?;
        if let Some(existing) = self.plan.type_literals.get(&node) {
            return if existing == &planned {
                Ok(())
            } else {
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidLiteralType(node),
                ))
            };
        }
        self.plan.type_literals.insert(node, planned.clone());

        let pushed_alias = if let Some(alias) = alias_owner {
            if self
                .active_structural_aliases
                .iter()
                .any(|(active, _)| *active == alias)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported {
                        node,
                        symbol: alias,
                    },
                ));
            }
            self.active_structural_aliases
                .push((alias, self.function_indirection_depth));
            true
        } else {
            false
        };
        let result = planned
            .property_type_nodes()
            .try_for_each(|property| self.plan_type_node_in_context(property, None, false));
        if pushed_alias {
            assert_eq!(
                self.active_structural_aliases.pop().map(|(alias, _)| alias),
                alias_owner
            );
        }
        result
    }

    fn plan_function_type(
        &mut self,
        node: NodeRef,
        alias_owner: Option<SemanticSymbolId>,
    ) -> Result<(), DeclaredTypeError> {
        let alias_is_generic = alias_owner.is_some_and(|alias| {
            self.plan
                .aliases
                .get(&alias)
                .is_some_and(|plan| !plan.type_parameters.is_empty())
        });
        let planned = functions::plan_function_type(
            self.store,
            self.host,
            node,
            alias_owner,
            alias_is_generic,
            self.array_targets,
        )
        .map_err(function_type_error)?;
        if let Some(existing) = self.plan.functions.get(&node) {
            return if existing == &planned {
                Ok(())
            } else {
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidFunctionType(node),
                ))
            };
        }
        self.plan.functions.insert(node, planned.clone());
        if let Some(proof) = functions::pending_function_type_proof(self.store, &planned)
            .map_err(function_type_error)?
            && !self.plan.pending_function_proofs.contains(&proof)
        {
            self.plan.pending_function_proofs.push(proof);
        }
        self.function_indirection_depth = self
            .function_indirection_depth
            .checked_add(1)
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(node)))?;
        let result = planned.parameters.iter().try_for_each(|parameter| {
            self.plan_type_node_in_context(parameter.type_node, None, false)
        });
        self.function_indirection_depth -= 1;
        result
    }

    fn plan_function_return_type(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        let return_type = self
            .plan
            .functions
            .get(&node)
            .map(|function| function.return_type)
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(node)))?;
        self.plan_type_node_in_context(return_type, None, false)
    }

    fn plan_property_interface(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<(), DeclaredTypeError> {
        let symbol = self
            .store
            .get_merged_symbol(symbol)
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::SymbolNotOwned(symbol),
            ))?;
        if self.plan.interfaces.contains_key(&symbol) {
            return Ok(());
        }
        let declaration = self
            .store
            .symbol(symbol)
            .and_then(|record| record.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::MissingDeclarations(symbol),
            ))?;
        if self.host.source(declaration).is_none() {
            return Ok(());
        }
        let planned = object_members::plan_interface(self.store, self.host, symbol)
            .map_err(property_object_error)?;
        self.plan.interfaces.insert(symbol, planned.clone());
        if !self.planning_interfaces.insert(symbol) {
            return Ok(());
        }
        let result = planned
            .property_type_nodes()
            .try_for_each(|property| self.plan_type_node_in_context(property, None, false));
        assert!(self.planning_interfaces.remove(&symbol));
        result
    }

    fn plan_union_type(
        &mut self,
        node: NodeRef,
        alias_symbol: Option<SemanticSymbolId>,
    ) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::UnionTypeNode(union) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidUnionType(node),
            ));
        };
        if union.types.nodes.len() < 2
            || union.types.has_trailing_comma
            || union.types.range != record.range
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidUnionType(node),
            ));
        }
        let mut types = Vec::with_capacity(union.types.nodes.len());
        let mut previous_end = record.range.start;
        for child in &union.types.nodes {
            let child = NodeRef::new(node.arena, node.file, *child);
            let child_record = preflight_node(self.store, self.host, child)?;
            if child_record.parent != Some(node.node)
                || child_record.range.start < previous_end
                || child_record.range.start < record.range.start
                || child_record.range.end > record.range.end
                || types.contains(&child)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidUnionType(node),
                ));
            }
            previous_end = child_record.range.end;
            self.plan_type_node_in_context(child, None, true)?;
            types.push(child);
        }
        let derived_alias = self.direct_union_alias(node)?;
        if alias_symbol.is_some() && derived_alias != alias_symbol {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidUnionType(node),
            ));
        }
        let planned = PlannedUnionType {
            types,
            alias_symbol: alias_symbol.or(derived_alias),
        };
        if let Some(existing) = self.plan.unions.insert(node, planned.clone())
            && existing != planned
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidUnionType(node),
            ));
        }
        Ok(())
    }

    fn direct_union_alias(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, DeclaredTypeError> {
        let mut child = node;
        loop {
            let Some(parent) = preflight_node(self.store, self.host, child)?.parent else {
                return Ok(None);
            };
            let parent = NodeRef::new(node.arena, node.file, parent);
            let record = preflight_node(self.store, self.host, parent)?;
            match &record.data {
                NodeData::ParenthesizedTypeNode(parenthesized)
                    if parenthesized.type_ == child.node =>
                {
                    child = parent;
                }
                NodeData::TypeAliasDeclaration(alias)
                    if record.kind == SyntaxKind::TypeAliasDeclaration
                        && alias.type_ == child.node =>
                {
                    let bound = self.host.bound_file(parent).ok_or({
                        DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::MissingOrForeignFacts(parent),
                        )
                    })?;
                    // `symbol` is the canonical declaration/export owner. The
                    // distinct `local_symbol` on an exported declaration is a
                    // local placeholder whose `export_symbol` points here; it
                    // must not own the type alias identity.
                    let symbol = bound
                        .symbol(parent)
                        .and_then(|symbol| self.store.get_merged_symbol(symbol))
                        .ok_or_else(|| {
                            type_node_unavailable(TypeNodeUnavailable::InvalidTypeAliasDeclaration(
                                parent,
                            ))
                        })?;
                    let flags = self
                        .store
                        .symbol(symbol)
                        .map(ts_binder::semantic::Symbol::flags)
                        .ok_or(DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::SymbolNotOwned(symbol),
                        ))?;
                    if !self.host.symbol_matches(self.store, parent, symbol)
                        || !flags.contains(SymbolFlags::TYPE_ALIAS)
                        || malformed_alias_merge(flags)
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidTypeAliasDeclaration(parent),
                        ));
                    }
                    if alias
                        .type_parameters
                        .as_ref()
                        .is_some_and(|parameters| !parameters.nodes.is_empty())
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
                        ));
                    }
                    return Ok(Some(symbol));
                }
                _ => return Ok(None),
            }
        }
    }

    fn cached_type_alias_rhs(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<CachedTypeAliasRhs, DeclaredTypeError> {
        if self.store.get_merged_symbol(symbol) != Some(symbol) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        let Some(declaration) = self
            .store
            .symbol(symbol)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
        else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        };
        if self.host.source(declaration).is_none() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        let declaration_record = preflight_node(self.store, self.host, declaration)?;
        let NodeData::TypeAliasDeclaration(alias) = &declaration_record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
            ));
        };
        if declaration_record.kind != SyntaxKind::TypeAliasDeclaration
            || !self.host.symbol_matches(self.store, declaration, symbol)
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
            ));
        }

        let mut type_node = NodeRef::new(declaration.arena, declaration.file, alias.type_);
        if preflight_node(self.store, self.host, type_node)?.parent != Some(declaration.node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
            ));
        }
        loop {
            let record = preflight_node(self.store, self.host, type_node)?;
            if record.kind != SyntaxKind::ParenthesizedType {
                return Ok(match record.kind {
                    SyntaxKind::UnionType => CachedTypeAliasRhs::DirectUnion,
                    SyntaxKind::TypeReference => CachedTypeAliasRhs::TypeReference(type_node),
                    SyntaxKind::TypeLiteral => CachedTypeAliasRhs::TypeLiteral(type_node),
                    SyntaxKind::FunctionType => CachedTypeAliasRhs::FunctionType(type_node),
                    _ => CachedTypeAliasRhs::NonUnion,
                });
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidParenthesizedType(type_node),
                ));
            };
            let inner = NodeRef::new(type_node.arena, type_node.file, parenthesized.type_);
            if preflight_node(self.store, self.host, inner)?.parent != Some(type_node.node) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidParenthesizedType(type_node),
                ));
            }
            type_node = inner;
        }
    }

    fn validate_cached_type_alias_identity(
        &self,
        root_symbol: SemanticSymbolId,
        cached: CachedTypeAlias,
        union_constituent: bool,
    ) -> Result<(), DeclaredTypeError> {
        let declared_type = cached.declared_type;
        let declared_data = self.store.type_payload(declared_type).map(TypeRecord::data);
        let remains_union = matches!(declared_data, Some(TypeData::Union(_)));
        let cached_array_capability_error =
            self.validate_cached_array_capability(declared_type).err();
        if let Some(error) = cached_array_capability_error
            && !matches!(error, LiteralTypeCacheError::UnsupportedUnionConstituent(_))
        {
            return Err(type_construction_error(error));
        }
        let mut current_missing_generic_metadata = cached.missing_generic_metadata;
        if union_constituent
            || matches!(
                declared_data,
                Some(TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::Union(_))
            )
        {
            self.validate_cached_union_result(declared_type, None)
                .map_err(type_construction_error)?;
        }

        let mut symbol = root_symbol;
        let mut visited = HashMap::new();
        let mut path = Vec::new();
        let mut missing_generic_metadata = HashSet::new();
        loop {
            if let Some(cycle_start) = visited.get(&symbol).copied() {
                if remains_union {
                    return Err(type_construction_error(
                        LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                    ));
                }
                let is_canonical_cycle_error = self
                    .store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| declared_type == bootstrap.error_type);
                let cycle = &path[cycle_start..];
                let missing_metadata_is_on_cycle = missing_generic_metadata
                    .iter()
                    .all(|missing| cycle.contains(missing));
                return if is_canonical_cycle_error && missing_metadata_is_on_cycle {
                    Ok(())
                } else {
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                    ))
                };
            }
            visited.insert(symbol, path.len());
            path.push(symbol);
            if current_missing_generic_metadata {
                missing_generic_metadata.insert(symbol);
            }
            let has_host_declaration = self
                .store
                .symbol(symbol)
                .and_then(|symbol| symbol.declarations())
                .and_then(|declarations| declarations.first())
                .is_some_and(|declaration| self.host.source(*declaration).is_some());
            if !has_host_declaration {
                // Fully cached queries intentionally support an empty host.
                // The canonical semantic identity and its complete cached
                // array-capability closure were validated above; AST RHS
                // provenance is enforced whenever its owner is available.
                if let Some(error) = cached_array_capability_error {
                    return Err(type_construction_error(error));
                }
                return if missing_generic_metadata.is_empty() {
                    Ok(())
                } else {
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                    ))
                };
            }
            match self.cached_type_alias_rhs(symbol)? {
                CachedTypeAliasRhs::DirectUnion => {
                    if !missing_generic_metadata.is_empty() {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    // A syntactic union may reduce to one reference. Recheck
                    // that surviving identity through the active union
                    // capability so a canonical array cannot leak into a
                    // later context-free session. Other reduced declared
                    // objects retain their existing declared-type validator.
                    if remains_union || matches!(declared_data, Some(TypeData::TypeReference(_))) {
                        self.validate_cached_union_result(declared_type, Some(symbol))
                            .map_err(type_construction_error)?;
                    }
                    return Ok(());
                }
                CachedTypeAliasRhs::NonUnion => {
                    if !missing_generic_metadata.is_empty() {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    if remains_union {
                        return Err(type_construction_error(
                            LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                        ));
                    }
                    return Ok(());
                }
                CachedTypeAliasRhs::TypeLiteral(type_literal) => {
                    if !missing_generic_metadata.is_empty()
                        || remains_union
                        || self
                            .store
                            .type_node_links(type_literal)
                            .and_then(|links| links.resolved_type)
                            != Some(declared_type)
                        || !matches!(declared_data, Some(TypeData::Object(_)))
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    return Ok(());
                }
                CachedTypeAliasRhs::FunctionType(function_type) => {
                    if !missing_generic_metadata.is_empty()
                        || remains_union
                        || self
                            .store
                            .type_node_links(function_type)
                            .and_then(|links| links.resolved_type)
                            != Some(declared_type)
                        || !matches!(declared_data, Some(TypeData::Object(_)))
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    return Ok(());
                }
                CachedTypeAliasRhs::TypeReference(reference) => {
                    if self
                        .store
                        .type_node_links(reference)
                        .and_then(|links| links.resolved_type)
                        != Some(declared_type)
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    let Some(target) = self
                        .store
                        .symbol_node_links(reference)
                        .and_then(|links| links.resolved_symbol)
                    else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    };
                    let Some(canonical) = self.store.get_merged_symbol(target) else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedSymbol {
                                node: reference,
                                symbol: target,
                            },
                        ));
                    };
                    if target != canonical {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedSymbol {
                                node: reference,
                                symbol: target,
                            },
                        ));
                    }
                    if let Some(name) = self.builtin_array_reference_name(reference)? {
                        if let Some(array_target) =
                            self.authoritative_global_array_target(canonical, reference)?
                        {
                            if !missing_generic_metadata.is_empty() || remains_union {
                                return Err(type_node_unavailable(
                                    TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                                ));
                            }
                            let arguments = self.type_reference_argument_nodes(reference)?;
                            let is_error = self
                                .store
                                .intrinsic_bootstrap()
                                .is_some_and(|bootstrap| declared_type == bootstrap.error_type);
                            if arguments.len() != 1 {
                                return if is_error {
                                    Ok(())
                                } else {
                                    Err(type_node_unavailable(
                                        TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                                    ))
                                };
                            }
                            validate_generic_global_type_instantiation(
                                self.store,
                                array_target,
                                declared_type,
                            )
                            .map_err(|_| {
                                type_node_unavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(
                                    root_symbol,
                                ))
                            })?;
                            let cached_argument =
                                generic_global_instantiation_argument(self.store, declared_type)
                                    .expect("the generic-global cache was preflighted");
                            return if self.cached_array_element_identity(arguments[0])?
                                == Some(cached_argument)
                            {
                                Ok(())
                            } else {
                                Err(type_node_unavailable(
                                    TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                                ))
                            };
                        }
                        if self.array_targets.is_none()
                            && self.global_symbol_has_name(canonical, name)
                        {
                            return Err(type_node_unavailable(
                                TypeNodeUnavailable::TypeArgumentsUnsupported(reference),
                            ));
                        }
                    }
                    let flags = self
                        .store
                        .symbol(canonical)
                        .map(ts_binder::semantic::Symbol::flags)
                        .ok_or(DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::SymbolNotOwned(canonical),
                        ))?;
                    if !flags.contains(SymbolFlags::TYPE_ALIAS) || malformed_alias_merge(flags) {
                        if !missing_generic_metadata.is_empty() {
                            return Err(type_node_unavailable(
                                TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                            ));
                        }
                        if remains_union {
                            return Err(type_construction_error(
                                LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                            ));
                        }
                        return Ok(());
                    }
                    let Some(target_cached) = cached_type_alias(
                        self.store,
                        self.host,
                        canonical,
                        self.strict_builtin_iterator_return,
                    )?
                    else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    };
                    let has_type_arguments = self.type_reference_argument_count(reference)? != 0;
                    if target_cached.type_parameter_count != 0 || has_type_arguments {
                        if !missing_generic_metadata.is_empty()
                            || target_cached.missing_generic_metadata
                        {
                            current_missing_generic_metadata =
                                target_cached.missing_generic_metadata;
                            symbol = canonical;
                            continue;
                        }
                        let is_error = self
                            .store
                            .intrinsic_bootstrap()
                            .is_some_and(|bootstrap| declared_type == bootstrap.error_type);
                        if self.cached_type_reference_has_arity_error(
                            reference,
                            canonical,
                            target_cached.type_parameter_count,
                        )? {
                            return if is_error {
                                Ok(())
                            } else {
                                Err(type_node_unavailable(
                                    TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                                ))
                            };
                        }
                        let is_cached_instantiation = if target_cached.type_parameter_count == 0 {
                            false
                        } else {
                            let key = self.cached_type_reference_instantiation_key(
                                root_symbol,
                                reference,
                                symbol,
                                canonical,
                                target_cached.type_parameter_count,
                            )?;
                            self.store
                                .type_alias_links(canonical)
                                .and_then(|links| links.instantiations.as_ref())
                                .and_then(|instantiations| instantiations.get(&key))
                                .is_some_and(|instantiation| *instantiation == declared_type)
                        };
                        if is_cached_instantiation {
                            return Ok(());
                        }
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    }
                    current_missing_generic_metadata = target_cached.missing_generic_metadata;
                    if target_cached.declared_type != declared_type {
                        return Err(type_construction_error(
                            LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                        ));
                    }
                    symbol = canonical;
                }
            }
        }
    }

    fn type_reference_argument_nodes(
        &self,
        reference: NodeRef,
    ) -> Result<Vec<NodeRef>, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, reference)?;
        let NodeData::TypeReferenceNode(reference_data) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference),
            ));
        };
        let name = NodeRef::new(reference.arena, reference.file, reference_data.type_name);
        let name_node = preflight_node(self.store, self.host, name)?;
        if name_node.parent != Some(reference.node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference),
            ));
        }
        let Some(arguments) = &reference_data.type_arguments else {
            return Ok(Vec::new());
        };
        if arguments.nodes.is_empty()
            || arguments.has_trailing_comma
            || arguments.range.start < name_node.range.end
            || arguments.range.end != record.range.end
            || arguments.range.start >= arguments.range.end
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference),
            ));
        }
        let mut nodes = Vec::with_capacity(arguments.nodes.len());
        let mut previous_end = name_node.range.end;
        for argument in &arguments.nodes {
            let argument = NodeRef::new(reference.arena, reference.file, *argument);
            let argument_node = preflight_node(self.store, self.host, argument)?;
            if argument_node.parent != Some(reference.node)
                || argument_node.range.start < previous_end
                || argument_node.range.start <= arguments.range.start
                || argument_node.range.end >= arguments.range.end
                || argument_node.range.start < record.range.start
                || argument_node.range.end > record.range.end
                || nodes.contains(&argument)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(reference),
                ));
            }
            previous_end = argument_node.range.end;
            nodes.push(argument);
        }
        Ok(nodes)
    }

    fn type_reference_argument_count(
        &self,
        reference: NodeRef,
    ) -> Result<usize, DeclaredTypeError> {
        self.type_reference_argument_nodes(reference)
            .map(|nodes| nodes.len())
    }

    fn cached_type_node_identity(
        &self,
        root_symbol: SemanticSymbolId,
        node: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?;
        let intrinsic = match record.kind {
            SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
            SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
            SyntaxKind::StringKeyword => Some(bootstrap.string_type),
            SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
            SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
            SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
            SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
            SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
            SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
            SyntaxKind::NullKeyword => Some(bootstrap.null_type),
            SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
            SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
            SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
            _ => None,
        };
        if let Some(intrinsic) = intrinsic {
            return Ok(intrinsic);
        }
        if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
            let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
            if record.kind != SyntaxKind::ParenthesizedType
                || preflight_node(self.store, self.host, inner)?.parent != Some(node.node)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                ));
            }
            return self.cached_type_node_identity(root_symbol, inner);
        }
        if let NodeData::LiteralTypeNode(literal) = &record.data {
            let literal = NodeRef::new(node.arena, node.file, literal.literal);
            let literal_record = preflight_node(self.store, self.host, literal)?;
            if record.kind != SyntaxKind::LiteralType
                || literal_record.parent != Some(node.node)
                || literal_record.range != record.range
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                ));
            }
            if literal_record.kind == SyntaxKind::NullKeyword
                && matches!(literal_record.data, NodeData::KeywordExpression(_))
            {
                return Ok(bootstrap.null_type);
            }
        }
        let resolved = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol))
            })?;
        if self.store.type_payload(resolved).is_none() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
            ));
        }
        Ok(resolved)
    }

    fn cached_type_reference_instantiation_key(
        &self,
        root_symbol: SemanticSymbolId,
        reference: NodeRef,
        owner: SemanticSymbolId,
        target: SemanticSymbolId,
        target_parameter_count: usize,
    ) -> Result<CacheHashKey, DeclaredTypeError> {
        let mut type_arguments = Vec::new();
        for argument in self.type_reference_argument_nodes(reference)? {
            type_arguments.push(self.cached_type_node_identity(root_symbol, argument)?);
        }

        let owner_is_local = self.is_local_type_alias(owner)?;
        let target_has_host_declaration = self
            .store
            .symbol(target)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .is_some_and(|declaration| self.host.source(*declaration).is_some());
        let target_is_local =
            owner_is_local && target_has_host_declaration && self.is_local_type_alias(target)?;
        if target_parameter_count != 0 && owner_is_local && !target_is_local {
            return Ok(type_alias_instantiation_cache_key(&type_arguments, None));
        }

        let owner_cached = cached_type_alias(
            self.store,
            self.host,
            owner,
            self.strict_builtin_iterator_return,
        )?
        .ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol))
        })?;
        let owner_arguments = self
            .store
            .type_alias_links(owner)
            .and_then(|links| links.type_parameters.as_ref())
            .cloned()
            .unwrap_or_default();
        if owner_cached.missing_generic_metadata
            || owner_arguments.len() != owner_cached.type_parameter_count
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
            ));
        }
        let owner_global = self
            .store
            .symbol_store()
            .assigned_global_symbol_id(owner)
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol))
            })?;
        Ok(type_alias_instantiation_cache_key(
            &type_arguments,
            Some((owner_global, &owner_arguments)),
        ))
    }

    fn cached_type_reference_has_arity_error(
        &self,
        reference: NodeRef,
        target: SemanticSymbolId,
        parameter_count: usize,
    ) -> Result<bool, DeclaredTypeError> {
        let argument_count = self.type_reference_argument_count(reference)?;
        if parameter_count == 0 {
            return Ok(argument_count != 0);
        }
        let declaration = self
            .store
            .symbol(target)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingTypeAliasDeclaration(target))
            })?;
        let declaration_node = preflight_node(self.store, self.host, declaration)?;
        let NodeData::TypeAliasDeclaration(alias) = &declaration_node.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
            ));
        };
        let parameters = alias.type_parameters.as_ref().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidTypeAliasDeclaration(
                declaration,
            ))
        })?;
        if parameters.nodes.len() != parameter_count {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(target),
            ));
        }
        let mut minimum = 0;
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
            let parameter_node = preflight_node(self.store, self.host, parameter)?;
            let NodeData::TypeParameterDeclaration(parameter) = &parameter_node.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            };
            if parameter.default_type.is_none() {
                minimum = index + 1;
            }
        }
        Ok(argument_count < minimum || argument_count > parameter_count)
    }

    #[allow(clippy::too_many_lines)] // Keeps the pinned literal grammar and provenance checks linear.
    fn plan_literal_type(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::LiteralTypeNode(literal) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(node),
            ));
        };
        let literal = NodeRef::new(node.arena, node.file, literal.literal);
        let literal_node = preflight_node(self.store, self.host, literal)?;
        if literal_node.parent != Some(node.node) || literal_node.range != record.range {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(node),
            ));
        }
        if literal_node.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(TypeNodeUnavailable::JsDoc(literal)));
        }

        let planned = match literal_node.kind {
            SyntaxKind::NullKeyword
                if matches!(literal_node.data, NodeData::KeywordExpression(_)) =>
            {
                PlannedLiteralType::Null
            }
            SyntaxKind::TrueKeyword
                if matches!(literal_node.data, NodeData::KeywordExpression(_)) =>
            {
                PlannedLiteralType::Boolean(true)
            }
            SyntaxKind::FalseKeyword
                if matches!(literal_node.data, NodeData::KeywordExpression(_)) =>
            {
                PlannedLiteralType::Boolean(false)
            }
            SyntaxKind::StringLiteral => {
                let NodeData::StringLiteral(data) = &literal_node.data else {
                    unreachable!("preflight_node validates syntax-kind payloads")
                };
                if data.token_flags.0 != 0 {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidLiteralType(node),
                    ));
                }
                PlannedLiteralType::String(data.text.clone())
            }
            SyntaxKind::NoSubstitutionTemplateLiteral => {
                let NodeData::NoSubstitutionTemplateLiteral(data) = &literal_node.data else {
                    unreachable!("preflight_node validates syntax-kind payloads")
                };
                if data.token_flags.0 != 0 || data.template_flags.0 != 0 {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidLiteralType(node),
                    ));
                }
                PlannedLiteralType::String(data.text.clone())
            }
            SyntaxKind::NumericLiteral => PlannedLiteralType::Number {
                value: self.preflight_numeric_literal(node, literal)?,
                unary_operand: None,
            },
            SyntaxKind::BigIntLiteral => PlannedLiteralType::BigInt {
                value: self.preflight_bigint_literal(node, literal)?,
                unary_operand: None,
            },
            SyntaxKind::PrefixUnaryExpression => {
                let NodeData::PrefixUnaryExpression(prefix) = &literal_node.data else {
                    unreachable!("preflight_node validates syntax-kind payloads")
                };
                if prefix.operator != SyntaxKind::MinusToken {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidLiteralType(node),
                    ));
                }
                let operand = NodeRef::new(node.arena, node.file, prefix.operand);
                let operand_node = preflight_node(self.store, self.host, operand)?;
                if operand_node.parent != Some(literal.node)
                    || operand_node.flags.0 & NODE_FLAG_JSDOC != 0
                {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidLiteralType(node),
                    ));
                }
                match operand_node.kind {
                    SyntaxKind::NumericLiteral => {
                        let positive = self.preflight_numeric_literal(node, operand)?;
                        PlannedLiteralType::Number {
                            value: -positive,
                            unary_operand: Some(positive),
                        }
                    }
                    SyntaxKind::BigIntLiteral => {
                        let positive = self.preflight_bigint_literal(node, operand)?;
                        PlannedLiteralType::BigInt {
                            value: PseudoBigInt::new(&positive.base10_value, true),
                            unary_operand: Some(positive),
                        }
                    }
                    _ => {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidLiteralType(node),
                        ));
                    }
                }
            }
            _ => {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidLiteralType(node),
                ));
            }
        };

        if let Some(existing) = self.plan.literals.insert(node, planned.clone()) {
            assert_eq!(existing, planned, "one literal type node has one value");
        }
        Ok(())
    }

    fn preflight_numeric_literal(
        &self,
        owner: NodeRef,
        literal: NodeRef,
    ) -> Result<Number, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, literal)?;
        let NodeData::NumericLiteral(data) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(owner),
            ));
        };
        if data.token_flags.0 != 0 || !self.source_spelling_matches(literal, &data.text) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(owner),
            ));
        }
        let normalized = normalize_numeric_separators(&data.text)
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidLiteralType(owner)))?;
        let value = ts_jsnum::from_string(&normalized);
        if value.is_nan() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(owner),
            ));
        }
        Ok(value)
    }

    fn preflight_bigint_literal(
        &self,
        owner: NodeRef,
        literal: NodeRef,
    ) -> Result<PseudoBigInt, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, literal)?;
        let NodeData::BigIntLiteral(data) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(owner),
            ));
        };
        if data.token_flags.0 != 0 || !self.source_spelling_matches(literal, &data.text) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(owner),
            ));
        }
        let normalized = normalize_bigint_literal(&data.text)
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidLiteralType(owner)))?;
        Ok(PseudoBigInt::parse_valid(&normalized))
    }

    fn source_spelling_matches(&self, node: NodeRef, expected: &str) -> bool {
        let Some((arena, _)) = self.host.source(node) else {
            return false;
        };
        let Some(source) = arena.source_text() else {
            return true;
        };
        let Some(record) = arena.get(node.node) else {
            return false;
        };
        source.get(record.range.start.get() as usize..record.range.end.get() as usize)
            == Some(expected)
    }

    fn plan_type_reference(
        &mut self,
        node: NodeRef,
        alias_owner: Option<SemanticSymbolId>,
        union_constituent: bool,
    ) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::TypeReferenceNode(reference) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };

        let name = NodeRef::new(node.arena, node.file, reference.type_name);
        let name_node = preflight_node(self.store, self.host, name)?;
        if name_node.parent != Some(node.node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        if name_node.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(TypeNodeUnavailable::JsDoc(name)));
        }
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::QualifiedTypeReference(node),
            ));
        };
        let mut type_arguments = Vec::new();
        let mut previous_end = name_node.range.end;
        if let Some(arguments) = &reference.type_arguments {
            if arguments.nodes.is_empty()
                || arguments.has_trailing_comma
                || arguments.range.start < name_node.range.end
                || arguments.range.end != record.range.end
                || arguments.range.start >= arguments.range.end
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ));
            }
            for argument in &arguments.nodes {
                let argument = NodeRef::new(node.arena, node.file, *argument);
                let argument_node = preflight_node(self.store, self.host, argument)?;
                if argument_node.parent != Some(node.node)
                    || argument_node.range.start < previous_end
                    || argument_node.range.start <= arguments.range.start
                    || argument_node.range.end >= arguments.range.end
                    || argument_node.range.start < record.range.start
                    || argument_node.range.end > record.range.end
                    || type_arguments.contains(&argument)
                {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidTypeReference(node),
                    ));
                }
                previous_end = argument_node.range.end;
                type_arguments.push(argument);
            }
        }

        let cached_type = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        let mut cached_pending_function = false;
        let cached_array_capability_missing = if let Some(cached) = cached_type {
            match self.validate_cached_array_capability(cached) {
                Ok(()) => false,
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(_)) => true,
                Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                    if self.is_pending_stored_function_type(type_) =>
                {
                    cached_pending_function = true;
                    false
                }
                Err(error) => return Err(type_construction_error(error)),
            }
        } else {
            false
        };
        let cached_syntax_contains_builtin_array = cached_type.is_some()
            && self.type_node_contains_builtin_array_reference(node, &mut HashSet::new())?;

        if !union_constituent
            && cached_type.is_some()
            && !cached_array_capability_missing
            && !cached_pending_function
            && !cached_syntax_contains_builtin_array
            && !self.cached_property_interface_reference(node)
            && !matches!(identifier.text.as_str(), "Array" | "ReadonlyArray")
        {
            return Ok(());
        }

        let cached_symbol = self
            .store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol);
        let possible_global_array_name = self.array_targets.is_some()
            && matches!(identifier.text.as_str(), "Array" | "ReadonlyArray");
        let symbol = if possible_global_array_name {
            let resolved = self.resolve_uncached_type_reference_symbol(node)?;
            let canonical = self.store.get_merged_symbol(resolved).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol {
                    node,
                    symbol: resolved,
                })
            })?;
            if let Some(cached) = cached_symbol {
                let cached_canonical = self.store.get_merged_symbol(cached).ok_or_else(|| {
                    type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol {
                        node,
                        symbol: cached,
                    })
                })?;
                if cached_canonical != canonical {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedSymbol {
                            node,
                            symbol: cached,
                        },
                    ));
                }
            }
            canonical
        } else if let Some(symbol) = cached_symbol {
            self.store.get_merged_symbol(symbol).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol { node, symbol })
            })?
        } else {
            let (arena, bound) = self.host.source(node).ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(node))
            })?;
            let mut callback_host = self.host.name_resolver_host(self.store)?;
            let resolved = CanonicalNameResolver::new(
                arena,
                bound,
                self.store.symbol_store(),
                &mut callback_host,
            )?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(name)),
                &identifier.text,
                SymbolFlags::TYPE,
                None,
                true,
                false,
            );
            // The production callback is intentionally a no-op in this cut.
            // Once symbol-use tracking becomes stateful, planning must retain
            // and replay the callback only after the full preflight succeeds.
            match resolved {
                Ok(Some(symbol)) => self.store.symbol(symbol).map(|_| symbol).ok_or({
                    DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
                })?,
                Ok(None) => {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::MissingTypeReference(node),
                    ));
                }
                Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias)) => {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::ImportAliasTypeReference { node, alias },
                    ));
                }
                Err(error) => return Err(error.into()),
            }
        };
        let global_array_target = self.authoritative_global_array_target(symbol, node)?;

        let flags = self
            .store
            .symbol(symbol)
            .ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
            })?
            .flags();
        if malformed_alias_merge(flags) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }

        if flags.contains(SymbolFlags::TYPE_ALIAS)
            && self
                .active_structural_aliases
                .iter()
                .find_map(|(active, depth)| (*active == symbol).then_some(*depth))
                .is_some_and(|depth| self.function_indirection_depth <= depth)
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
            ));
        }

        if union_constituent
            && global_array_target.is_none()
            && !flags.contains(SymbolFlags::TYPE_ALIAS)
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(node),
            ));
        }

        if global_array_target.is_none() || type_arguments.len() == 1 {
            for argument in &type_arguments {
                self.plan_type_node_in_context(*argument, None, false)?;
            }
        }

        let mut effective_alias_owner = alias_owner;
        let arity = if global_array_target.is_some() {
            if type_arguments.len() == 1 {
                PlannedTypeReferenceArity::Valid
            } else {
                PlannedTypeReferenceArity::InvalidGeneric {
                    minimum: 1,
                    maximum: 1,
                }
            }
        } else if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            let local_count =
                preflight_class_or_interface_reference(self.store, self.host, symbol, flags)?;
            if local_count != 0 || !type_arguments.is_empty() {
                return Err(type_node_unavailable(if type_arguments.is_empty() {
                    TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol }
                } else {
                    TypeNodeUnavailable::TypeArgumentsUnsupported(node)
                }));
            }
            if flags.contains(SymbolFlags::INTERFACE) && !flags.contains(SymbolFlags::CLASS) {
                self.plan_property_interface(symbol)?;
            }
            PlannedTypeReferenceArity::Valid
        } else if flags.contains(SymbolFlags::TYPE_PARAMETER) {
            preflight_type_parameter_symbol(self.store, self.host, symbol, &mut HashSet::new())?;
            if type_arguments.is_empty() {
                PlannedTypeReferenceArity::Valid
            } else {
                PlannedTypeReferenceArity::NotGeneric
            }
        } else if flags.contains(SymbolFlags::TYPE_ALIAS) {
            let type_parameter_count = self.plan_type_alias(symbol, union_constituent)?;
            if type_parameter_count != 0
                && let Some(owner) = alias_owner
                && !self.is_local_type_alias(symbol)?
                && self.is_local_type_alias(owner)?
            {
                effective_alias_owner = None;
            }
            if type_parameter_count == 0 {
                if type_arguments.is_empty() {
                    PlannedTypeReferenceArity::Valid
                } else {
                    PlannedTypeReferenceArity::NotGeneric
                }
            } else {
                let parameters = self
                    .plan
                    .aliases
                    .get(&symbol)
                    .ok_or_else(|| {
                        type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(
                            symbol,
                        ))
                    })?
                    .type_parameters
                    .clone();
                let minimum = parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(index, parameter)| {
                        parameter.default_type.is_none().then_some(index + 1)
                    })
                    .max()
                    .unwrap_or(0);
                if type_arguments.len() < minimum || type_arguments.len() > type_parameter_count {
                    PlannedTypeReferenceArity::InvalidGeneric {
                        minimum,
                        maximum: type_parameter_count,
                    }
                } else {
                    for (index, parameter) in
                        parameters.iter().enumerate().skip(type_arguments.len())
                    {
                        let default_type = parameter.default_type.ok_or_else(|| {
                            type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(
                                symbol,
                            ))
                        })?;
                        let default_key = (symbol, default_type);
                        if !self.planning_defaults.insert(default_key) {
                            return Err(type_node_unavailable(
                                TypeNodeUnavailable::CircularGenericAliasDefault {
                                    alias: symbol,
                                    default_type,
                                },
                            ));
                        }
                        let result = (|| {
                            self.plan_type_node_in_context(default_type, None, false)?;
                            self.validate_generic_alias_default_references(
                                symbol,
                                default_type,
                                &parameters[..index],
                                &parameters,
                            )?;
                            self.validate_planned_direct_alias_node(
                                symbol,
                                default_type,
                                None,
                                &mut HashSet::new(),
                            )
                        })();
                        assert!(self.planning_defaults.remove(&default_key));
                        result?;
                    }
                    let alias_type = self
                        .plan
                        .aliases
                        .get(&symbol)
                        .ok_or_else(|| {
                            type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(
                                symbol,
                            ))
                        })?
                        .type_node;
                    self.validate_planned_direct_alias_node(
                        symbol,
                        alias_type,
                        Some(symbol),
                        &mut HashSet::from([symbol]),
                    )?;
                    PlannedTypeReferenceArity::Valid
                }
            }
        } else if flags.contains(SymbolFlags::ALIAS) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::ImportAliasTypeReference {
                    node,
                    alias: symbol,
                },
            ));
        } else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedReferenceTarget { node, symbol },
            ));
        };

        if let Some(target) = global_array_target
            && let Some(cached) = self
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
        {
            if arity == PlannedTypeReferenceArity::Valid {
                validate_generic_global_type_instantiation(self.store, target, cached).map_err(
                    |_| type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)),
                )?;
                let cached_argument = generic_global_instantiation_argument(self.store, cached)
                    .expect("the generic-global cache was preflighted");
                if self.cached_array_element_identity(type_arguments[0])? != Some(cached_argument) {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidTypeReference(node),
                    ));
                }
            } else if self
                .store
                .intrinsic_bootstrap()
                .is_none_or(|bootstrap| cached != bootstrap.error_type)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ));
            }
        }

        let planned = PlannedTypeReference {
            symbol,
            type_arguments,
            alias_owner: effective_alias_owner,
            arity,
            global_array_target,
        };
        if let Some(existing) = self.plan.references.insert(node, planned.clone()) {
            assert_eq!(existing, planned, "one type-reference node has one plan");
        }
        if cached_pending_function && let Some(cached) = cached_type {
            self.validate_cached_array_capability(cached)
                .map_err(type_construction_error)?;
        }
        Ok(())
    }

    fn authoritative_global_array_target(
        &self,
        symbol: SemanticSymbolId,
        node: NodeRef,
    ) -> Result<Option<TypeId>, DeclaredTypeError> {
        let Some(targets) = self.array_targets else {
            return Ok(None);
        };
        let mut previous = None;
        for target in [targets.array_type(), targets.readonly_array_type()] {
            if previous == Some(target) {
                continue;
            }
            previous = Some(target);
            let record = self.store.type_payload(target).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
            })?;
            let Some(target_symbol) = record.symbol() else {
                continue;
            };
            let target_symbol = self.store.get_merged_symbol(target_symbol).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
            })?;
            if target_symbol == symbol {
                preflight_generic_global_type_target(self.store, target).map_err(|_| {
                    type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
                })?;
                return Ok(Some(target));
            }
        }
        Ok(None)
    }

    fn builtin_array_reference_name(
        &self,
        reference: NodeRef,
    ) -> Result<Option<&'static str>, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, reference)?;
        let NodeData::TypeReferenceNode(reference_data) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference),
            ));
        };
        let name = NodeRef::new(reference.arena, reference.file, reference_data.type_name);
        let name_node = preflight_node(self.store, self.host, name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Ok(None);
        };
        if name_node.parent != Some(reference.node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference),
            ));
        }
        Ok(match identifier.text.as_str() {
            "Array" => Some("Array"),
            "ReadonlyArray" => Some("ReadonlyArray"),
            _ => None,
        })
    }

    fn global_symbol_has_name(&self, symbol: SemanticSymbolId, name: &str) -> bool {
        self.store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| self.store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source(name))
            .and_then(|global| self.store.get_merged_symbol(global))
            == Some(symbol)
    }

    fn cached_property_interface_reference(&self, node: NodeRef) -> bool {
        let cached_type_is_interface = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
            .and_then(|type_| self.store.type_payload(type_))
            .is_some_and(|record| {
                matches!(record.data(), TypeData::Interface(_))
                    && record.object_flags().contains(ObjectFlags::INTERFACE)
                    && !record.object_flags().contains(ObjectFlags::CLASS)
            });
        let cached_symbol_is_interface = self
            .store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            .and_then(|symbol| self.store.get_merged_symbol(symbol))
            .and_then(|symbol| self.store.symbol(symbol))
            .is_some_and(|record| {
                record.flags().contains(SymbolFlags::INTERFACE)
                    && !record.flags().contains(SymbolFlags::CLASS)
            });
        cached_type_is_interface || cached_symbol_is_interface
    }

    fn validate_generic_alias_default_references(
        &self,
        alias: SemanticSymbolId,
        default_type: NodeRef,
        earlier_parameters: &[PlannedTypeParameter],
        alias_parameters: &[PlannedTypeParameter],
    ) -> Result<(), DeclaredTypeError> {
        let (arena, _) = self.host.source(default_type).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(
                default_type,
            ))
        })?;
        for (node, record) in arena.iter() {
            if record.kind != SyntaxKind::TypeReference {
                continue;
            }
            let reference = NodeRef::new(arena.id(), default_type.file, node);
            if !self.node_is_within(reference, default_type)? {
                continue;
            }
            let symbol = if let Some(planned) = self.plan.references.get(&reference) {
                planned.symbol
            } else {
                let cached = self
                    .store
                    .symbol_node_links(reference)
                    .and_then(|links| links.resolved_symbol)
                    .ok_or_else(|| {
                        type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeReference(
                            reference,
                        ))
                    })?;
                self.store.get_merged_symbol(cached).ok_or_else(|| {
                    type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol {
                        node: reference,
                        symbol: cached,
                    })
                })?
            };
            let flags = self
                .store
                .symbol(symbol)
                .map(ts_binder::semantic::Symbol::flags)
                .ok_or(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::SymbolNotOwned(symbol),
                ))?;
            if flags.contains(SymbolFlags::TYPE_PARAMETER)
                && alias_parameters
                    .iter()
                    .any(|parameter| parameter.symbol == symbol)
                && !earlier_parameters
                    .iter()
                    .any(|parameter| parameter.symbol == symbol)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported {
                        alias,
                        default_type,
                        referenced_parameter: symbol,
                    },
                ));
            }
        }
        Ok(())
    }

    fn validate_planned_direct_alias_node(
        &self,
        alias: SemanticSymbolId,
        node: NodeRef,
        alias_body: Option<SemanticSymbolId>,
        visited_aliases: &mut HashSet<SemanticSymbolId>,
    ) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        match &record.data {
            NodeData::ParenthesizedTypeNode(parenthesized) => self
                .validate_planned_direct_alias_node(
                    alias,
                    NodeRef::new(node.arena, node.file, parenthesized.type_),
                    alias_body,
                    visited_aliases,
                ),
            NodeData::TypeReferenceNode(_) => {
                let reference_symbol = if let Some(reference) = self.plan.references.get(&node) {
                    reference.symbol
                } else if let Some(cached) = self
                    .store
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol)
                {
                    self.store.get_merged_symbol(cached).ok_or_else(|| {
                        type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol {
                            node,
                            symbol: cached,
                        })
                    })?
                } else {
                    self.resolve_uncached_type_reference_symbol(node)?
                };
                let flags = self
                    .store
                    .symbol(reference_symbol)
                    .map(ts_binder::semantic::Symbol::flags)
                    .ok_or(DeclaredTypeError::Unavailable(
                        DeclaredTypeUnavailable::SymbolNotOwned(reference_symbol),
                    ))?;
                if !flags.contains(SymbolFlags::TYPE_ALIAS)
                    || !visited_aliases.insert(reference_symbol)
                {
                    return Ok(());
                }
                if let Some(target) = self.plan.aliases.get(&reference_symbol) {
                    return self.validate_planned_direct_alias_node(
                        alias,
                        target.type_node,
                        Some(reference_symbol),
                        visited_aliases,
                    );
                }
                let declared_type = self
                    .store
                    .type_alias_links(reference_symbol)
                    .and_then(|links| links.declared_type)
                    .ok_or_else(|| {
                        type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(
                            reference_symbol,
                        ))
                    })?;
                if self
                    .store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| declared_type == bootstrap.intrinsic_marker_type)
                    && !symbol_is_builtin_iterator_return(self.store, reference_symbol)
                {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                            alias,
                            declared_type,
                        },
                    ));
                }
                Ok(())
            }
            NodeData::UnionTypeNode(_) => {
                let union = self.plan.unions.get(&node).ok_or_else(|| {
                    type_node_unavailable(TypeNodeUnavailable::MissingPlannedUnionType(node))
                })?;
                for constituent in &union.types {
                    self.validate_planned_direct_alias_node(
                        alias,
                        *constituent,
                        None,
                        visited_aliases,
                    )?;
                }
                Ok(())
            }
            _ if record.kind == SyntaxKind::IntrinsicKeyword
                && alias_body
                    .is_none_or(|owner| !symbol_is_builtin_iterator_return(self.store, owner)) =>
            {
                let declared_type = self
                    .store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.intrinsic_marker_type)
                    .ok_or(DeclaredTypeError::Unavailable(
                        DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
                    ))?;
                Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                        alias,
                        declared_type,
                    },
                ))
            }
            _ => Ok(()),
        }
    }

    fn resolve_uncached_type_reference_symbol(
        &self,
        node: NodeRef,
    ) -> Result<SemanticSymbolId, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::TypeReferenceNode(reference) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        let name = NodeRef::new(node.arena, node.file, reference.type_name);
        let name_node = preflight_node(self.store, self.host, name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::QualifiedTypeReference(node),
            ));
        };
        if name_node.parent != Some(node.node) || name_node.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        let (arena, bound) = self.host.source(node).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(node))
        })?;
        let mut callback_host = self.host.name_resolver_host(self.store)?;
        match CanonicalNameResolver::new(
            arena,
            bound,
            self.store.symbol_store(),
            &mut callback_host,
        )?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(name)),
            &identifier.text,
            SymbolFlags::TYPE,
            None,
            true,
            false,
        ) {
            Ok(Some(symbol)) => self.store.symbol(symbol).map(|_| symbol).ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
            }),
            Ok(None) => Err(type_node_unavailable(
                TypeNodeUnavailable::MissingTypeReference(node),
            )),
            Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias)) => {
                Err(type_node_unavailable(
                    TypeNodeUnavailable::ImportAliasTypeReference { node, alias },
                ))
            }
            Err(error) => Err(error.into()),
        }
    }

    fn node_is_within(
        &self,
        mut node: NodeRef,
        ancestor: NodeRef,
    ) -> Result<bool, DeclaredTypeError> {
        let mut visited = HashSet::new();
        loop {
            if node == ancestor {
                return Ok(true);
            }
            if !visited.insert(node) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ));
            }
            let Some(parent) = preflight_node(self.store, self.host, node)?.parent else {
                return Ok(false);
            };
            node = NodeRef::new(node.arena, node.file, parent);
        }
    }

    fn is_local_type_alias(&self, symbol: SemanticSymbolId) -> Result<bool, DeclaredTypeError> {
        let mut current = self
            .store
            .symbol(symbol)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol))
            })?;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(current) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(current),
                ));
            }
            let record = preflight_node(self.store, self.host, current)?;
            if matches!(
                record.kind,
                SyntaxKind::FunctionDeclaration
                    | SyntaxKind::FunctionExpression
                    | SyntaxKind::ArrowFunction
                    | SyntaxKind::MethodDeclaration
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor
                    | SyntaxKind::Constructor
            ) {
                return Ok(true);
            }
            let Some(parent) = record.parent else {
                return Ok(false);
            };
            current = NodeRef::new(current.arena, current.file, parent);
        }
    }

    fn plan_type_alias(
        &mut self,
        symbol: SemanticSymbolId,
        union_constituent: bool,
    ) -> Result<usize, DeclaredTypeError> {
        let cached = cached_type_alias(
            self.store,
            self.host,
            symbol,
            self.strict_builtin_iterator_return,
        )?;
        if let Some(plan) = self.plan.aliases.get(&symbol) {
            if let Some(cached) = cached {
                self.validate_cached_type_alias_identity(symbol, cached, union_constituent)?;
            }
            return Ok(cached.map_or(plan.type_parameters.len(), |cached| {
                cached.type_parameter_count
            }));
        }

        let mut cached_pending_function = false;
        if let Some(cached) = cached {
            match self.validate_cached_type_alias_identity(symbol, cached, union_constituent) {
                Ok(()) => {}
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedUnionType(type_),
                )) if self.is_pending_stored_function_type(type_) => {
                    cached_pending_function = true;
                }
                Err(error) => return Err(error),
            }
        }

        let record = self.store.symbol(symbol).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
        })?;
        let flags = record.flags();
        if !flags.contains(SymbolFlags::TYPE_ALIAS) || malformed_alias_merge(flags) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasSymbol(symbol),
            ));
        }
        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol))
            })?
            .to_vec();
        if declarations.len() != 1 {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasSymbol(symbol),
            ));
        }
        if let Some(cached_alias) = cached
            && declarations
                .first()
                .is_some_and(|declaration| self.host.source(*declaration).is_none())
        {
            self.validate_cached_type_alias_identity(symbol, cached_alias, union_constituent)?;
            return Ok(cached_alias.type_parameter_count);
        }

        let cached_array_capability_missing = if let Some(cached) = cached {
            match self.validate_cached_array_capability(cached.declared_type) {
                Ok(()) => false,
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(_)) => true,
                Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                    if self.is_pending_stored_function_type(type_) =>
                {
                    cached_pending_function = true;
                    false
                }
                Err(error) => return Err(type_construction_error(error)),
            }
        } else {
            false
        };

        let mut first = None;
        let mut type_parameters = Vec::new();
        let mut checked = HashSet::new();
        for declaration in declarations {
            let declaration_node = preflight_node(self.store, self.host, declaration)?;
            if declaration_node.kind == SyntaxKind::JsTypeAliasDeclaration {
                return Err(type_node_unavailable(TypeNodeUnavailable::JsDocTypeAlias(
                    declaration,
                )));
            }
            let NodeData::TypeAliasDeclaration(alias) = &declaration_node.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            };
            if declaration_node.kind != SyntaxKind::TypeAliasDeclaration
                || !self.host.symbol_matches(self.store, declaration, symbol)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            }
            let name = NodeRef::new(declaration.arena, declaration.file, alias.name);
            let type_node = NodeRef::new(declaration.arena, declaration.file, alias.type_);
            let name_node = preflight_node(self.store, self.host, name)?;
            let type_record = preflight_node(self.store, self.host, type_node)?;
            let NodeData::Identifier(identifier) = &name_node.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            };
            if name_node.parent != Some(declaration.node)
                || type_record.parent != Some(declaration.node)
                || declaration_node.flags.0 & NODE_FLAG_JSDOC != 0
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            }
            let parameter_symbols = explicit_type_parameter_symbols(
                self.store,
                self.host,
                declaration,
                alias.type_parameters.as_ref(),
                &mut checked,
            )?;
            if let Some(parameters) = &alias.type_parameters {
                if parameters.nodes.len() != parameter_symbols.len() {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                    ));
                }
                for (parameter, parameter_symbol) in parameters.nodes.iter().zip(parameter_symbols)
                {
                    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
                    let parameter_node = preflight_node(self.store, self.host, parameter)?;
                    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_node.data
                    else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                        ));
                    };
                    if parameter_node.parent != Some(declaration.node) {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                        ));
                    }
                    if parameter_data.constraint.is_some() {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::GenericAliasConstraintUnsupported {
                                alias: symbol,
                                parameter,
                            },
                        ));
                    }
                    let default_type = parameter_data.default_type.map(|default_type| {
                        NodeRef::new(declaration.arena, declaration.file, default_type)
                    });
                    if let Some(default_type) = default_type
                        && preflight_node(self.store, self.host, default_type)?.parent
                            != Some(parameter.node)
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                        ));
                    }
                    let planned = PlannedTypeParameter {
                        symbol: parameter_symbol,
                        default_type,
                    };
                    if !type_parameters.contains(&planned) {
                        type_parameters.push(planned);
                    }
                }
            }
            if first.is_none() {
                first = Some((name, identifier.text.clone(), type_node));
            }
        }

        let Some((name, name_text, type_node)) = first else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol),
            ));
        };
        let type_parameter_count =
            cached.map_or(type_parameters.len(), |cached| cached.type_parameter_count);
        self.plan.aliases.insert(
            symbol,
            TypeAliasPlan {
                name,
                name_text,
                type_node,
                type_parameters,
            },
        );
        if cached.is_none()
            || cached_array_capability_missing
            || cached_pending_function
            || self.direct_type_literal_rhs(type_node)?
            || self.direct_function_type_rhs(type_node)?
            || self.type_node_contains_builtin_array_reference(type_node, &mut HashSet::new())?
        {
            self.plan_type_node_in_context(type_node, Some(symbol), union_constituent)?;
        }
        if cached_pending_function && let Some(cached) = cached {
            self.validate_cached_type_alias_identity(symbol, cached, union_constituent)?;
        }
        Ok(type_parameter_count)
    }

    fn type_node_contains_builtin_array_reference(
        &self,
        node: NodeRef,
        visited: &mut HashSet<NodeRef>,
    ) -> Result<bool, DeclaredTypeError> {
        if !visited.insert(node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        let record = preflight_node(self.store, self.host, node)?;
        let result = match &record.data {
            NodeData::ParenthesizedTypeNode(parenthesized) => self
                .type_node_contains_builtin_array_reference(
                    NodeRef::new(node.arena, node.file, parenthesized.type_),
                    visited,
                )?,
            NodeData::ArrayTypeNode(_) => true,
            NodeData::TypeReferenceNode(_) => {
                if self.builtin_array_reference_name(node)?.is_some() {
                    true
                } else {
                    let mut contains = false;
                    for argument in self.type_reference_argument_nodes(node)? {
                        contains |=
                            self.type_node_contains_builtin_array_reference(argument, visited)?;
                    }
                    contains
                }
            }
            NodeData::UnionTypeNode(union) => {
                let mut contains = false;
                for child in &union.types.nodes {
                    contains |= self.type_node_contains_builtin_array_reference(
                        NodeRef::new(node.arena, node.file, *child),
                        visited,
                    )?;
                }
                contains
            }
            NodeData::TypeLiteralNode(literal) => {
                if record.kind != SyntaxKind::TypeLiteral
                    || literal.members.has_trailing_comma
                    || literal.members.range != record.range
                {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidLiteralType(node),
                    ));
                }
                let mut contains = false;
                let mut seen = HashSet::with_capacity(literal.members.nodes.len());
                for member in &literal.members.nodes {
                    let member = NodeRef::new(node.arena, node.file, *member);
                    let member_record = preflight_node(self.store, self.host, member)?;
                    if member_record.parent != Some(node.node) || !seen.insert(member) {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidLiteralType(node),
                        ));
                    }
                    let type_node = match (member_record.kind, &member_record.data) {
                        (
                            SyntaxKind::PropertyDeclaration,
                            NodeData::PropertyDeclaration(property),
                        ) => property.type_,
                        (
                            SyntaxKind::PropertySignature,
                            NodeData::PropertySignatureDeclaration(property),
                        ) => Some(property.type_),
                        _ => {
                            return Err(type_node_unavailable(
                                TypeNodeUnavailable::UnsupportedSyntax {
                                    node: member,
                                    kind: member_record.kind,
                                },
                            ));
                        }
                    }
                    .ok_or_else(|| {
                        type_node_unavailable(TypeNodeUnavailable::InvalidLiteralType(node))
                    })?;
                    let type_node = NodeRef::new(member.arena, member.file, type_node);
                    if preflight_node(self.store, self.host, type_node)?.parent != Some(member.node)
                    {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidLiteralType(node),
                        ));
                    }
                    contains |=
                        self.type_node_contains_builtin_array_reference(type_node, visited)?;
                }
                contains
            }
            NodeData::FunctionTypeNode(function) => {
                if record.kind != SyntaxKind::FunctionType {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidFunctionType(node),
                    ));
                }
                let mut contains = false;
                for parameter in &function.parameters.nodes {
                    let parameter = NodeRef::new(node.arena, node.file, *parameter);
                    let parameter_record = preflight_node(self.store, self.host, parameter)?;
                    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data
                    else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidFunctionType(node),
                        ));
                    };
                    let Some(type_node) = parameter_data.type_ else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidFunctionType(node),
                        ));
                    };
                    contains |= self.type_node_contains_builtin_array_reference(
                        NodeRef::new(node.arena, node.file, type_node),
                        visited,
                    )?;
                }
                let Some(return_type) = function.type_ else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidFunctionType(node),
                    ));
                };
                contains |= self.type_node_contains_builtin_array_reference(
                    NodeRef::new(node.arena, node.file, return_type),
                    visited,
                )?;
                contains
            }
            _ => false,
        };
        assert!(visited.remove(&node));
        Ok(result)
    }

    fn direct_type_literal_rhs(&self, mut node: NodeRef) -> Result<bool, DeclaredTypeError> {
        loop {
            let record = preflight_node(self.store, self.host, node)?;
            if record.kind == SyntaxKind::TypeLiteral {
                return Ok(true);
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                return Ok(false);
            };
            node = NodeRef::new(node.arena, node.file, parenthesized.type_);
        }
    }

    fn direct_function_type_rhs(&self, mut node: NodeRef) -> Result<bool, DeclaredTypeError> {
        loop {
            let record = preflight_node(self.store, self.host, node)?;
            if record.kind == SyntaxKind::FunctionType {
                return Ok(true);
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                return Ok(false);
            };
            node = NodeRef::new(node.arena, node.file, parenthesized.type_);
        }
    }
}

pub(super) struct CanonicalTypeQuery<'store, 'host, 'arena, 'diagnostics> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    array_type: Option<TypeId>,
    global_types: Option<CanonicalGlobalTypes>,
    options: CanonicalTypeQueryOptions,
    diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
    resolving_property_interfaces: HashSet<SemanticSymbolId>,
    pending_function_parameters: Vec<FunctionTypePlan>,
}

impl<'store, 'host, 'arena, 'diagnostics> CanonicalTypeQuery<'store, 'host, 'arena, 'diagnostics> {
    /// Opens a query session over one store and diagnostic owner.
    ///
    /// # Errors
    ///
    /// Returns a typed option mismatch when the store was already claimed by
    /// a checker session with a different strict iterator-return mode.
    pub(super) fn new(
        store: &'store mut CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        options: impl Into<CanonicalTypeQueryOptions>,
        diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
    ) -> Result<Self, DeclaredTypeError> {
        let options = options.into();
        if let Err(established) =
            store.claim_strict_builtin_iterator_return(options.strict_builtin_iterator_return)
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::CheckerOptionMismatch {
                    established_strict_builtin_iterator_return: established,
                    requested_strict_builtin_iterator_return: options
                        .strict_builtin_iterator_return,
                },
            ));
        }
        Ok(Self {
            store,
            host,
            array_type: None,
            global_types: None,
            options,
            diagnostics,
            resolving_property_interfaces: HashSet::new(),
            pending_function_parameters: Vec::new(),
        })
    }

    /// Opens a query with the context-owned standard-library identities. Only
    /// this capability may enable `T[]`; an ordinary query continues to fail
    /// closed instead of discovering or synthesizing an `Array` lookalike.
    pub(super) fn new_with_global_types(
        store: &'store mut CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        global_types: &CanonicalGlobalTypes,
        options: impl Into<CanonicalTypeQueryOptions>,
        diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
    ) -> Result<Self, DeclaredTypeError> {
        let array_type = global_types.array_type;
        let mut query = Self::new(store, host, options, diagnostics)?;
        query.array_type = Some(array_type);
        query.global_types = Some(global_types.clone());
        Ok(query)
    }

    #[cfg(test)]
    fn new_with_array_type_for_test(
        store: &'store mut CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        array_type: TypeId,
        options: impl Into<CanonicalTypeQueryOptions>,
        diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
    ) -> Result<Self, DeclaredTypeError> {
        let mut query = Self::new(store, host, options, diagnostics)?;
        query.array_type = Some(array_type);
        Ok(query)
    }

    /// Resolves one dependency-closed type-node query.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable or provenance error before mutation when
    /// the node's dependency closure is outside the installed semantic cut.
    pub(super) fn get_type_from_type_node(
        &mut self,
        node: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        if !self.pending_function_parameters.is_empty() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionType(node),
            ));
        }
        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            self.global_types
                .as_ref()
                .map(CanonicalArrayTargets::from_global_types),
            self.options.strict_builtin_iterator_return,
        );
        let direct_alias = planner.direct_type_alias_owner(node)?;
        planner.plan_type_node(node)?;
        let plan = planner.finish();
        let mut prepared = self.prepare_literal_types(&plan)?;
        if let Err(error) = self.seed_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        let direct_function_alias = direct_alias.filter(|alias| {
            plan.aliases.get(alias).is_some_and(|alias| {
                self.direct_function_type_plan_node(alias.type_node, &plan)
                    .is_some()
            })
        });
        let result = match direct_function_alias {
            Some(alias) => self.execute_declared_type(alias, &plan, &mut prepared),
            None => self.execute_type_node(node, &plan, &mut prepared),
        };
        self.complete_type_query(result, &plan, &mut prepared)
    }

    /// Resolves one exact annotated `FunctionDeclaration` or `ArrowFunction` into
    /// the callable value owned by its binder FUNCTION symbol.
    pub(super) fn get_type_of_source_callable(
        &mut self,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        if !self.pending_function_parameters.is_empty() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionType(declaration),
            ));
        }
        let array_targets = self
            .global_types
            .as_ref()
            .map(CanonicalArrayTargets::from_global_types);
        let family = match preflight_node(self.store, self.host, declaration)?.kind {
            SyntaxKind::FunctionDeclaration => SourceCallableFamily::FunctionDeclaration,
            SyntaxKind::ArrowFunction => SourceCallableFamily::ArrowFunction,
            kind => {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::UnsupportedSyntax {
                        node: declaration,
                        kind,
                    },
                ));
            }
        };
        let callable = source_callables::plan_source_callable(
            self.store,
            self.host,
            declaration,
            owner_symbol,
            array_targets,
        )
        .map_err(|error| source_callable_error(error, family))?;
        if let source_callables::SourceCallableState::Resolved { type_, .. } =
            source_callables::source_callable_state(self.store, &callable, true)
                .map_err(|error| source_callable_error(error, callable.family))?
        {
            return Ok(type_);
        }

        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            array_targets,
            self.options.strict_builtin_iterator_return,
        );
        for parameter in &callable.parameters {
            planner.plan_type_node(parameter.type_node)?;
        }
        let plan = planner.finish();
        let (cold_source_types, source_optional_unions) =
            source_callables::reserve_source_callable_capacities(self.store, &[&callable])
                .map_err(|error| source_callable_error(error, callable.family))?;
        let mut prepared = self.prepare_literal_types_with_additional(
            &plan,
            source_optional_unions,
            cold_source_types,
        )?;
        if let Err(error) = self.seed_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        let pending = match source_callables::begin_source_callable(self.store, &callable)
            .map_err(|error| source_callable_error(error, callable.family))?
        {
            Ok(pending) => pending,
            Err(resolved) => {
                self.pending_function_parameters.clear();
                prepared.clear_pending_function_types();
                return Ok(resolved);
            }
        };
        if let Err(error) =
            source_callables::finalize_source_callable_structure(self.store, &callable, pending)
                .map_err(|error| source_callable_error(error, callable.family))
        {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        if callable.parameters.is_empty() {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return match source_callables::source_callable_state(self.store, &callable, false)
                .map_err(|error| source_callable_error(error, callable.family))?
            {
                source_callables::SourceCallableState::Resolved { type_, .. }
                    if type_ == pending.type_ =>
                {
                    Ok(type_)
                }
                _ => Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidFunctionType(declaration),
                )),
            };
        }

        let mut base_types = Vec::with_capacity(callable.parameters.len());
        for parameter in &callable.parameters {
            match self.execute_type_node(parameter.type_node, &plan, &mut prepared) {
                Ok(type_) => base_types.push(type_),
                Err(error) => {
                    self.pending_function_parameters.clear();
                    prepared.clear_pending_function_types();
                    return Err(error);
                }
            }
        }
        if let Err(error) = self.flush_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        let publication = source_callables::publish_source_callable_parameter_types(
            self.store,
            self.global_types.as_ref(),
            &[PendingSourceCallableParameterTypes {
                plan: callable.clone(),
                base_types,
            }],
            &mut prepared,
        )
        .map_err(|error| source_callable_error(error, callable.family));
        self.pending_function_parameters.clear();
        prepared.clear_pending_function_types();
        publication?;
        Ok(pending.type_)
    }

    /// Resolves the explicitly annotated return type of an exact function-type
    /// signature. Return annotations remain lazy after the function object and
    /// its parameter value types have been published.
    pub(super) fn get_return_type_of_signature(
        &mut self,
        signature: SignatureId,
    ) -> Result<TypeId, DeclaredTypeError> {
        if !self.pending_function_parameters.is_empty() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(signature),
            ));
        }
        let declaration = self
            .store
            .signature(signature)
            .and_then(Signature::declaration)
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
            })?;
        match preflight_node(self.store, self.host, declaration)?.kind {
            SyntaxKind::FunctionDeclaration | SyntaxKind::ArrowFunction => {
                return self.get_return_type_of_source_callable_signature(signature, declaration);
            }
            SyntaxKind::FunctionType => {}
            _ => {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidFunctionSignature(signature),
                ));
            }
        }

        let mut parameter_planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            self.global_types
                .as_ref()
                .map(CanonicalArrayTargets::from_global_types),
            self.options.strict_builtin_iterator_return,
        );
        parameter_planner.plan_type_node(declaration)?;
        let parameter_plan = parameter_planner.finish();
        let parameter_function = parameter_plan
            .functions
            .get(&declaration)
            .cloned()
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
            })?;
        functions::validate_function_type_signature_identity(
            self.store,
            &parameter_function,
            signature,
        )
        .map_err(|error| function_signature_error(error, signature))?;
        let mut parameter_prepared = self.prepare_literal_types(&parameter_plan)?;
        if let Err(error) =
            self.seed_pending_function_parameters(&parameter_plan, &mut parameter_prepared)
        {
            self.pending_function_parameters.clear();
            parameter_prepared.clear_pending_function_types();
            return Err(error);
        }
        let parameter_result =
            self.flush_pending_function_parameters(&parameter_plan, &mut parameter_prepared);
        self.pending_function_parameters.clear();
        parameter_prepared.clear_pending_function_types();
        parameter_result?;

        if let Some(return_type) =
            functions::validate_lazy_return_signature(self.store, &parameter_function, signature)
                .map_err(|error| function_signature_error(error, signature))?
        {
            return Ok(return_type);
        }

        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            self.global_types
                .as_ref()
                .map(CanonicalArrayTargets::from_global_types),
            self.options.strict_builtin_iterator_return,
        );
        planner.plan_type_node(declaration)?;
        planner.plan_function_return_type(declaration)?;
        let plan = planner.finish();
        let function = plan.functions.get(&declaration).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
        })?;
        if let Some(return_type) =
            functions::validate_lazy_return_signature(self.store, &function, signature)
                .map_err(|error| function_signature_error(error, signature))?
        {
            return Ok(return_type);
        }

        let mut prepared = self.prepare_literal_types(&plan)?;
        if !self.store.try_reserve_circular_return_signatures(1) {
            prepared.clear_pending_function_types();
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(signature),
            ));
        }
        if !self.store.push_type_resolution(
            TypeResolutionTarget::Signature(signature),
            TypeSystemPropertyName::ResolvedReturnType,
        )? {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return self.error_type();
        }
        if let Err(error) = self.seed_pending_function_parameters(&plan, &mut prepared) {
            let popped = self.store.pop_type_resolution();
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            if popped.is_none() {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidFunctionSignature(signature),
                ));
            }
            return Err(error);
        }
        let resolved = match self.execute_type_node(function.return_type, &plan, &mut prepared) {
            Ok(resolved) => resolved,
            Err(error) => {
                if self.store.pop_type_resolution().is_none() {
                    self.pending_function_parameters.clear();
                    prepared.clear_pending_function_types();
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidFunctionSignature(signature),
                    ));
                }
                self.pending_function_parameters.clear();
                prepared.clear_pending_function_types();
                return Err(error);
            }
        };
        let Some(cycle_free) = self.store.pop_type_resolution() else {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(signature),
            ));
        };
        if let Err(error) = self.flush_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        self.pending_function_parameters.clear();
        prepared.clear_pending_function_types();
        if cycle_free {
            functions::publish_lazy_return_type(self.store, &function, signature, resolved)
                .map_err(|error| function_signature_error(error, signature))
        } else {
            let return_type = functions::publish_circular_lazy_return_type(
                self.store, &function, signature, resolved,
            )
            .map_err(|error| function_signature_error(error, signature))?;
            self.diagnostics.add(
                Some(function.return_type),
                Diagnostic::new(
                    message_by_code(2577).expect("TS2577 is in the diagnostic catalog"),
                ),
            );
            Ok(return_type)
        }
    }

    fn get_return_type_of_source_callable_signature(
        &mut self,
        signature: SignatureId,
        declaration: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        let provenance = self
            .store
            .source_callable_type_for_signature(signature)
            .and_then(|type_| self.store.source_callable_provenance(type_))
            .filter(|provenance| {
                provenance.signature == signature && provenance.declaration == declaration
            })
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidFunctionSignature(signature))
            })?;
        let array_targets = self
            .global_types
            .as_ref()
            .map(CanonicalArrayTargets::from_global_types);
        let callable = source_callables::plan_source_callable(
            self.store,
            self.host,
            declaration,
            provenance.owner_symbol,
            array_targets,
        )
        .map_err(|error| source_callable_signature_error(error, provenance.family, signature))?;
        source_callables::validate_source_callable_signature_identity(
            self.store, &callable, signature,
        )
        .map_err(|error| source_callable_signature_error(error, callable.family, signature))?;
        if let Some(return_type) =
            source_callables::validate_lazy_source_callable_return(self.store, &callable, signature)
                .map_err(|error| {
                    source_callable_signature_error(error, callable.family, signature)
                })?
        {
            return Ok(return_type);
        }

        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            array_targets,
            self.options.strict_builtin_iterator_return,
        );
        planner.plan_type_node(callable.return_type)?;
        let plan = planner.finish();
        let mut prepared = self.prepare_literal_types(&plan)?;
        if !self.store.try_reserve_circular_return_signatures(1) {
            prepared.clear_pending_function_types();
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(signature),
            ));
        }
        if !self.store.push_type_resolution(
            TypeResolutionTarget::Signature(signature),
            TypeSystemPropertyName::ResolvedReturnType,
        )? {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return self.error_type();
        }
        if let Err(error) = self.seed_pending_function_parameters(&plan, &mut prepared) {
            let popped = self.store.pop_type_resolution();
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            if popped.is_none() {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidFunctionSignature(signature),
                ));
            }
            return Err(error);
        }
        let resolved = match self.execute_type_node(callable.return_type, &plan, &mut prepared) {
            Ok(resolved) => resolved,
            Err(error) => {
                if self.store.pop_type_resolution().is_none() {
                    self.pending_function_parameters.clear();
                    prepared.clear_pending_function_types();
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidFunctionSignature(signature),
                    ));
                }
                self.pending_function_parameters.clear();
                prepared.clear_pending_function_types();
                return Err(error);
            }
        };
        let Some(cycle_free) = self.store.pop_type_resolution() else {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(signature),
            ));
        };
        if let Err(error) = self.flush_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        self.pending_function_parameters.clear();
        prepared.clear_pending_function_types();
        if cycle_free {
            source_callables::publish_lazy_source_callable_return(
                self.store, &callable, signature, resolved,
            )
            .map_err(|error| source_callable_signature_error(error, callable.family, signature))
        } else {
            let return_type = source_callables::publish_circular_lazy_source_callable_return(
                self.store, &callable, signature, resolved,
            )
            .map_err(|error| source_callable_signature_error(error, callable.family, signature))?;
            self.diagnostics.add(
                Some(callable.return_type),
                Diagnostic::new(
                    message_by_code(2577).expect("TS2577 is in the diagnostic catalog"),
                ),
            );
            Ok(return_type)
        }
    }

    /// Resolves the declared type identity of one symbol.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable, resolution, or provenance error when the
    /// symbol's dependency closure cannot be resolved by this semantic cut.
    pub(super) fn get_declared_type_of_symbol(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        if !self.pending_function_parameters.is_empty() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        let symbol = self.canonical_symbol(symbol)?;
        let flags = self.symbol_flags(symbol)?;
        if malformed_alias_merge(flags) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }
        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            self.global_types
                .as_ref()
                .map(CanonicalArrayTargets::from_global_types),
            self.options.strict_builtin_iterator_return,
        );
        if !flags
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::TYPE_PARAMETER)
            && flags.contains(SymbolFlags::TYPE_ALIAS)
        {
            planner.plan_type_alias(symbol, false)?;
        } else if flags.contains(SymbolFlags::INTERFACE) && !flags.contains(SymbolFlags::CLASS) {
            planner.plan_property_interface(symbol)?;
        }
        let plan = planner.finish();
        let mut prepared = self.prepare_literal_types(&plan)?;
        if let Err(error) = self.seed_pending_function_parameters(&plan, &mut prepared) {
            self.pending_function_parameters.clear();
            prepared.clear_pending_function_types();
            return Err(error);
        }
        let result = self.execute_declared_type(symbol, &plan, &mut prepared);
        self.complete_type_query(result, &plan, &mut prepared)
    }

    fn seed_pending_function_parameters(
        &mut self,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<(), DeclaredTypeError> {
        for function in plan.functions.values() {
            if self
                .pending_function_parameters
                .iter()
                .any(|pending| pending.node == function.node)
            {
                continue;
            }
            let Some(pending) = functions::resumable_function_type(self.store, function)
                .map_err(function_type_error)?
            else {
                continue;
            };
            functions::finalize_function_structure(self.store, function, pending)
                .map_err(function_type_error)?;
            if function.parameters.is_empty() {
                continue;
            }
            let proof = functions::pending_function_type_proof(self.store, function)
                .map_err(function_type_error)?
                .ok_or_else(|| {
                    type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(function.node))
                })?;
            prepared
                .authorize_pending_function(self.store, &proof)
                .map_err(Self::literal_cache_error)?;
            self.pending_function_parameters.push(function.clone());
        }
        Ok(())
    }

    fn complete_type_query(
        &mut self,
        result: Result<TypeId, DeclaredTypeError>,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let result = match result {
            Ok(type_) => self
                .flush_pending_function_parameters(plan, prepared)
                .map(|()| type_),
            Err(error) => Err(error),
        };
        self.pending_function_parameters.clear();
        prepared.clear_pending_function_types();
        result
    }

    fn prepare_literal_types(
        &mut self,
        plan: &TypeQueryPlan,
    ) -> Result<PreparedTypeQueryTypes, DeclaredTypeError> {
        self.prepare_literal_types_with_additional(plan, 0, 0)
    }

    fn prepare_literal_types_with_additional(
        &mut self,
        plan: &TypeQueryPlan,
        additional_union_operations: usize,
        additional_source_types: usize,
    ) -> Result<PreparedTypeQueryTypes, DeclaredTypeError> {
        let mut strings = Vec::new();
        let mut numbers = Vec::new();
        let mut bigints = Vec::new();
        for (node, literal) in &plan.literals {
            if self
                .store
                .type_node_links(*node)
                .and_then(|links| links.resolved_type)
                .is_some()
            {
                continue;
            }
            match literal {
                PlannedLiteralType::String(value) => strings.push(value.clone()),
                PlannedLiteralType::Number {
                    value,
                    unary_operand,
                } => {
                    if let Some(operand) = unary_operand {
                        numbers.push(*operand);
                    }
                    numbers.push(*value);
                }
                PlannedLiteralType::BigInt {
                    value,
                    unary_operand,
                } => {
                    if let Some(operand) = unary_operand {
                        bigints.push(operand.clone());
                    }
                    bigints.push(value.clone());
                }
                PlannedLiteralType::Null | PlannedLiteralType::Boolean(_) => {}
            }
        }
        let unions = plan
            .unions
            .iter()
            .filter(|(node, _)| {
                self.store
                    .type_node_links(**node)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            })
            .map(|(_, union)| union)
            .collect::<Vec<_>>();
        let function_plans = plan.functions.values().collect::<Vec<_>>();
        let (cold_function_types, function_type_aliases, optional_parameter_unions) =
            functions::reserve_function_type_capacities(self.store, &function_plans)
                .map_err(function_type_error)?;
        let union_operation_count = unions
            .len()
            .checked_add(optional_parameter_unions)
            .and_then(|count| count.checked_add(additional_union_operations))
            .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        let named_unions = unions
            .iter()
            .filter(|union| union.alias_symbol.is_some())
            .count();
        let mut array_references_by_target = BTreeMap::<TypeId, (usize, NodeRef)>::new();
        for (node, array) in &plan.arrays {
            if array.fallback.is_some() {
                continue;
            }
            let target = self
                .array_type
                .expect("planned arrays have a global target");
            let entry = array_references_by_target
                .entry(target)
                .or_insert((0, *node));
            entry.0 = entry
                .0
                .checked_add(1)
                .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        }
        for (node, reference) in &plan.references {
            let Some(target) = reference.global_array_target else {
                continue;
            };
            if reference.arity != PlannedTypeReferenceArity::Valid
                || self
                    .store
                    .type_node_links(*node)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            {
                continue;
            }
            let entry = array_references_by_target
                .entry(target)
                .or_insert((0, *node));
            entry.0 = entry
                .0
                .checked_add(1)
                .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        }
        let array_references = array_references_by_target
            .values()
            .try_fold(0usize, |total, (count, _)| total.checked_add(*count))
            .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        let literal_values = strings
            .len()
            .checked_add(numbers.len())
            .and_then(|count| count.checked_add(bigints.len()))
            .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        let additional_types = literal_values
            .checked_add(union_operation_count)
            .and_then(|count| count.checked_mul(2))
            .and_then(|count| count.checked_add(array_references))
            .and_then(|count| count.checked_add(cold_function_types))
            .and_then(|count| count.checked_add(additional_source_types))
            .ok_or_else(|| Self::literal_cache_error(LiteralTypeCacheError::Capacity))?;
        if !self.store.try_reserve_types(additional_types) {
            return Err(Self::literal_cache_error(LiteralTypeCacheError::Capacity));
        }
        for (target, (count, node)) in array_references_by_target {
            if !self.store.try_reserve_object_instantiations(target, count) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ));
            }
        }
        self.store
            .prepare_type_query_types_with_pending_functions(
                &strings,
                &numbers,
                &bigints,
                union_operation_count,
                named_unions,
                self.global_types.as_ref(),
                &plan.pending_function_proofs,
                function_plans.len(),
                function_type_aliases,
            )
            .map_err(Self::literal_cache_error)
    }

    fn literal_cache_error(error: LiteralTypeCacheError) -> DeclaredTypeError {
        type_construction_error(error)
    }

    fn canonical_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, DeclaredTypeError> {
        self.store.get_merged_symbol(symbol).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
        })
    }

    fn symbol_flags(&self, symbol: SemanticSymbolId) -> Result<SymbolFlags, DeclaredTypeError> {
        self.store
            .symbol(symbol)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
            })
    }

    fn execute_declared_type(
        &mut self,
        symbol: SemanticSymbolId,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let flags = self.symbol_flags(symbol)?;
        let error_type = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?
            .error_type;
        if malformed_alias_merge(flags) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }
        if let Some(declared_type) =
            get_declared_class_interface_or_type_parameter(self.store, self.host, symbol, flags)?
        {
            if flags.contains(SymbolFlags::INTERFACE)
                && !flags.contains(SymbolFlags::CLASS)
                && plan.interfaces.contains_key(&symbol)
            {
                return self.execute_property_interface(symbol, declared_type, plan, prepared);
            }
            return Ok(declared_type);
        }
        if flags.contains(SymbolFlags::TYPE_ALIAS) {
            return self.execute_type_alias(symbol, plan, prepared);
        }
        if flags.intersects(SymbolFlags::ENUM) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(UnsupportedDeclaredTypeKind::Enum),
            ));
        }
        if flags.contains(SymbolFlags::ENUM_MEMBER) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::EnumMember,
                ),
            ));
        }
        if flags.contains(SymbolFlags::ALIAS) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::Alias,
                ),
            ));
        }
        Ok(error_type)
    }

    fn execute_property_interface(
        &mut self,
        symbol: SemanticSymbolId,
        declared_type: TypeId,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let interface =
            plan.interfaces
                .get(&symbol)
                .cloned()
                .ok_or(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::MissingDeclarations(symbol),
                ))?;
        let state = object_members::interface_state(self.store, &interface, declared_type)
            .map_err(property_object_error)?;
        if self.resolving_property_interfaces.contains(&symbol) {
            return Ok(declared_type);
        }
        if !self.resolving_property_interfaces.insert(symbol) {
            unreachable!("the active-interface check and insertion are adjacent")
        }
        let result = (|| {
            let mut types = Vec::with_capacity(interface.properties.len());
            for property in interface.property_type_nodes() {
                types.push(self.execute_type_node(property, plan, prepared)?);
            }
            if state.is_resolved() {
                object_members::validate_resolved_property_types(self.store, &interface, &types)
                    .map_err(property_object_error)?;
                Ok(declared_type)
            } else {
                object_members::publish_property_members(self.store, &interface, state, &types)
                    .map_err(property_object_error)
            }
        })();
        assert!(self.resolving_property_interfaces.remove(&symbol));
        result
    }

    fn execute_type_alias(
        &mut self,
        symbol: SemanticSymbolId,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(cached) = cached_type_alias(
            self.store,
            self.host,
            symbol,
            self.options.strict_builtin_iterator_return,
        )? {
            if let Some(alias) = plan.aliases.get(&symbol)
                && let Some(structural_node) = self
                    .direct_type_literal_plan_node(alias.type_node, plan)
                    .or_else(|| self.direct_function_type_plan_node(alias.type_node, plan))
                && !self
                    .pending_function_parameters
                    .iter()
                    .any(|pending| pending.node == structural_node)
            {
                let resolved = self.execute_type_node(alias.type_node, plan, prepared)?;
                if resolved != cached.declared_type {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
                    ));
                }
            }
            return Ok(cached.declared_type);
        }
        let alias = plan.aliases.get(&symbol).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeAlias(symbol))
        })?;
        let error_type = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?
            .error_type;
        if !self.store.push_type_resolution(
            TypeResolutionTarget::Symbol(symbol),
            TypeSystemPropertyName::DeclaredType,
        )? {
            return Ok(error_type);
        }

        let resolved = match self.execute_type_node(alias.type_node, plan, prepared) {
            Ok(resolved) => resolved,
            Err(error) => {
                if self.store.pop_type_resolution().is_none() {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::ResolutionStackInvariant(symbol),
                    ));
                }
                return Err(error);
            }
        };
        let cycle_free = self.store.pop_type_resolution().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::ResolutionStackInvariant(symbol))
        })?;

        let mut links = self
            .store
            .type_alias_links(symbol)
            .cloned()
            .unwrap_or_default();
        let declared_type = if cycle_free {
            if !alias.type_parameters.is_empty() {
                let type_parameters = alias
                    .type_parameters
                    .iter()
                    .map(|parameter| execute_type_parameter(self.store, parameter.symbol))
                    .collect::<Vec<_>>();
                let mut instantiations = HashMap::new();
                instantiations.insert(type_list_key(&type_parameters), resolved);
                links.type_parameters = Some(type_parameters);
                links.instantiations = Some(instantiations);
            }
            let intrinsic_marker = self
                .store
                .intrinsic_bootstrap()
                .expect("bootstrap was checked before alias resolution")
                .intrinsic_marker_type;
            if resolved == intrinsic_marker && alias.name_text == "BuiltinIteratorReturn" {
                let bootstrap = self
                    .store
                    .intrinsic_bootstrap()
                    .expect("bootstrap was checked before alias resolution");
                if self.options.strict_builtin_iterator_return {
                    bootstrap.undefined_type
                } else {
                    bootstrap.any_type
                }
            } else {
                resolved
            }
        } else {
            self.diagnostics.add(
                Some(alias.name),
                Diagnostic::with_arguments(
                    message_by_code(2456).expect("TS2456 is in the diagnostic catalog"),
                    [alias.name_text],
                ),
            );
            error_type
        };

        if links.declared_type.is_none() {
            links.declared_type = Some(declared_type);
        }
        let published = links
            .declared_type
            .expect("the alias declared type was just initialized");
        if !self.store.set_type_alias_links(symbol, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasSymbol(symbol),
            ));
        }
        Ok(published)
    }

    fn execute_type_node(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        match record.kind {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword => self.keyword_type(record.kind),
            SyntaxKind::ParenthesizedType => {
                let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                };
                self.execute_type_node(
                    NodeRef::new(node.arena, node.file, parenthesized.type_),
                    plan,
                    prepared,
                )
            }
            SyntaxKind::LiteralType => self.execute_literal_type(node, plan),
            SyntaxKind::ArrayType => self.execute_array_type(node, plan, prepared),
            SyntaxKind::TypeLiteral => self.execute_property_type_literal(node, plan, prepared),
            SyntaxKind::FunctionType => self.execute_function_type(node, plan, prepared),
            SyntaxKind::TypeReference => self.execute_type_reference(node, plan, prepared),
            SyntaxKind::UnionType => self.execute_union_type(node, plan, prepared),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
        }
    }

    fn execute_function_type(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(pending) = self
            .pending_function_parameters
            .iter()
            .find(|pending| pending.node == node)
        {
            return functions::active_alias_shell(self.store, pending).map_err(function_type_error);
        }
        let function =
            plan.functions.get(&node).cloned().ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(node))
            })?;
        let pending = match functions::begin_function_type(self.store, &function)
            .map_err(function_type_error)?
        {
            Ok(pending) => pending,
            Err(resolved) => return Ok(resolved),
        };
        functions::finalize_function_structure(self.store, &function, pending)
            .map_err(function_type_error)?;
        let resolved_type = pending.type_;
        if !function.parameters.is_empty() {
            let proof = functions::pending_function_type_proof(self.store, &function)
                .map_err(function_type_error)?
                .ok_or_else(|| {
                    type_node_unavailable(TypeNodeUnavailable::InvalidFunctionType(node))
                })?;
            prepared
                .authorize_pending_function(self.store, &proof)
                .map_err(Self::literal_cache_error)?;
            self.pending_function_parameters.push(function);
        }
        Ok(resolved_type)
    }

    fn flush_pending_function_parameters(
        &mut self,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<(), DeclaredTypeError> {
        let mut resolved = Vec::new();
        let mut index = 0usize;
        while index < self.pending_function_parameters.len() {
            let function = self.pending_function_parameters[index].clone();
            let mut base_types = Vec::with_capacity(function.parameters.len());
            for parameter in &function.parameters {
                base_types.push(self.execute_type_node(parameter.type_node, plan, prepared)?);
            }
            resolved.push(PendingParameterTypes {
                plan: function,
                base_types,
            });
            index += 1;
        }
        functions::publish_parameter_types(
            self.store,
            self.global_types.as_ref(),
            &resolved,
            prepared,
        )
        .map_err(function_type_error)?;
        self.pending_function_parameters.clear();
        Ok(())
    }

    fn execute_array_type(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let array = plan.arrays.get(&node).copied().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeReference(node))
        })?;
        let cached = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        if let Some(cached) = cached {
            return Ok(cached);
        }
        let resolved_type = if let Some(fallback) = array.fallback {
            fallback
        } else {
            let element_type = self.execute_type_node(array.element_type, plan, prepared)?;
            let array_type = self.array_type.ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::UnsupportedSyntax {
                    node,
                    kind: SyntaxKind::ArrayType,
                })
            })?;
            create_type_from_generic_global_type(
                self.store,
                array_type,
                element_type,
                ObjectFlags::FROM_TYPE_NODE,
            )
            .map_err(|_| type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)))?
        };
        let mut links = self
            .store
            .type_node_links(node)
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(resolved_type);
        if !self.store.set_type_node_links(node, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        Ok(resolved_type)
    }

    fn direct_type_literal_plan_node(
        &self,
        mut node: NodeRef,
        plan: &TypeQueryPlan,
    ) -> Option<NodeRef> {
        loop {
            if plan.type_literals.contains_key(&node) {
                return Some(node);
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &self.host.node(node)?.data else {
                return None;
            };
            node = NodeRef::new(node.arena, node.file, parenthesized.type_);
        }
    }

    fn direct_function_type_plan_node(
        &self,
        mut node: NodeRef,
        plan: &TypeQueryPlan,
    ) -> Option<NodeRef> {
        loop {
            if plan.functions.contains_key(&node) {
                return Some(node);
            }
            let NodeData::ParenthesizedTypeNode(parenthesized) = &self.host.node(node)?.data else {
                return None;
            };
            node = NodeRef::new(node.arena, node.file, parenthesized.type_);
        }
    }

    fn execute_property_type_literal(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let literal =
            plan.type_literals.get(&node).cloned().ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidLiteralType(node))
            })?;
        let state = object_members::ensure_type_literal_shell(self.store, &literal)
            .map_err(property_object_error)?;
        if matches!(state, PropertyObjectState::EmptyBootstrap(_)) {
            return Ok(state.type_id());
        }
        let mut types = Vec::with_capacity(literal.properties.len());
        for property in literal.property_type_nodes() {
            types.push(self.execute_type_node(property, plan, prepared)?);
        }
        if state.is_resolved() {
            object_members::validate_resolved_property_types(self.store, &literal, &types)
                .map_err(property_object_error)?;
            Ok(state.type_id())
        } else {
            object_members::publish_property_members(self.store, &literal, state, &types)
                .map_err(property_object_error)
        }
    }

    fn execute_union_type(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(resolved_type) = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        {
            return Ok(resolved_type);
        }
        let union = plan.unions.get(&node).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedUnionType(node))
        })?;
        let mut types = Vec::with_capacity(union.types.len());
        for constituent in union.types {
            types.push(self.execute_type_node(constituent, plan, prepared)?);
        }
        let resolved_type = match self.global_types.as_ref() {
            Some(global_types) => self.store.literal_union_type_prepared_with_global_types(
                global_types,
                &types,
                union.alias_symbol,
                prepared,
            ),
            None => self
                .store
                .literal_union_type_prepared(&types, union.alias_symbol, prepared),
        }
        .map_err(Self::literal_cache_error)?;
        let mut links = self
            .store
            .type_node_links(node)
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(resolved_type);
        if !self.store.set_type_node_links(node, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidUnionType(node),
            ));
        }
        Ok(resolved_type)
    }

    fn execute_literal_type(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
    ) -> Result<TypeId, DeclaredTypeError> {
        let literal = plan.literals.get(&node).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedLiteralType(node))
        })?;
        if matches!(literal, PlannedLiteralType::Null) {
            return self
                .store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.null_type)
                .ok_or(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
                ));
        }
        if let Some(resolved_type) = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        {
            return Ok(resolved_type);
        }

        let resolved_type = match literal {
            PlannedLiteralType::Null => unreachable!("null returns before the non-null cache"),
            PlannedLiteralType::String(value) => self
                .store
                .regular_string_literal_type(value)
                .map_err(Self::literal_cache_error)?,
            PlannedLiteralType::Number {
                value,
                unary_operand,
            } => {
                if let Some(operand) = unary_operand {
                    self.store
                        .regular_number_literal_type(operand)
                        .map_err(Self::literal_cache_error)?;
                }
                self.store
                    .regular_number_literal_type(value)
                    .map_err(Self::literal_cache_error)?
            }
            PlannedLiteralType::BigInt {
                value,
                unary_operand,
            } => {
                if let Some(operand) = unary_operand {
                    self.store
                        .regular_bigint_literal_type(operand)
                        .map_err(Self::literal_cache_error)?;
                }
                self.store
                    .regular_bigint_literal_type(value)
                    .map_err(Self::literal_cache_error)?
            }
            PlannedLiteralType::Boolean(value) => self
                .store
                .intrinsic_bootstrap()
                .map(|bootstrap| {
                    if value {
                        bootstrap.regular_true_type
                    } else {
                        bootstrap.regular_false_type
                    }
                })
                .ok_or(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
                ))?,
        };
        let mut links = self
            .store
            .type_node_links(node)
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(resolved_type);
        if !self.store.set_type_node_links(node, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidLiteralType(node),
            ));
        }
        Ok(resolved_type)
    }

    fn execute_type_reference(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let cached_resolved_type = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        let planned_reference = plan.references.get(&node);
        if let Some(resolved_type) = cached_resolved_type
            && !planned_reference.is_some_and(|reference| {
                reference.global_array_target.is_some()
                    || plan.interfaces.contains_key(&reference.symbol)
            })
        {
            return Ok(resolved_type);
        }
        let reference = planned_reference.cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeReference(node))
        })?;
        let symbol = reference.symbol;

        let mut symbol_links = self
            .store
            .symbol_node_links(node)
            .cloned()
            .unwrap_or_default();
        if let Some(cached) = symbol_links.resolved_symbol {
            let canonical = self.store.get_merged_symbol(cached).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol {
                    node,
                    symbol: cached,
                })
            })?;
            if canonical != symbol {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedSymbol {
                        node,
                        symbol: cached,
                    },
                ));
            }
        } else if cached_resolved_type.is_some() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedSymbol { node, symbol },
            ));
        }

        if let Some(cached) = cached_resolved_type
            && reference.global_array_target.is_some()
            && reference.arity != PlannedTypeReferenceArity::Valid
        {
            return Ok(cached);
        }

        let resolved_type = if let Some(target) = reference.global_array_target {
            match reference.arity {
                PlannedTypeReferenceArity::Valid => {
                    let [argument] = reference.type_arguments.as_slice() else {
                        unreachable!("a valid canonical array reference has one argument")
                    };
                    let argument = self.execute_type_node(*argument, plan, prepared)?;
                    create_type_from_generic_global_type(
                        self.store,
                        target,
                        argument,
                        ObjectFlags::FROM_TYPE_NODE,
                    )
                    .map_err(|_| {
                        type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
                    })?
                }
                PlannedTypeReferenceArity::NotGeneric
                | PlannedTypeReferenceArity::InvalidGeneric { .. } => {
                    self.issue_type_reference_arity_diagnostic(
                        node,
                        symbol,
                        reference.arity,
                        Some(target),
                    )?;
                    self.error_type()?
                }
            }
        } else {
            if reference.arity != PlannedTypeReferenceArity::Valid {
                for argument in &reference.type_arguments {
                    self.execute_type_node(*argument, plan, prepared)?;
                }
            }
            let declared_type = self.execute_declared_type(symbol, plan, prepared)?;
            match reference.arity {
                PlannedTypeReferenceArity::Valid => {
                    let alias_parameter_count = self
                        .store
                        .type_alias_links(symbol)
                        .and_then(|links| links.type_parameters.as_ref())
                        .map(Vec::len);
                    let is_type_alias =
                        self.symbol_flags(symbol)?.contains(SymbolFlags::TYPE_ALIAS);
                    if is_type_alias
                        && !reference.type_arguments.is_empty()
                        && alias_parameter_count.is_none()
                    {
                        self.issue_type_reference_arity_diagnostic(
                            node,
                            symbol,
                            PlannedTypeReferenceArity::NotGeneric,
                            None,
                        )?;
                        self.error_type()?
                    } else if is_type_alias
                        && (!reference.type_arguments.is_empty()
                            || alias_parameter_count.is_some_and(|count| count != 0))
                    {
                        self.execute_generic_alias_instantiation(
                            &reference,
                            declared_type,
                            plan,
                            prepared,
                        )?
                    } else {
                        declared_type
                    }
                }
                PlannedTypeReferenceArity::NotGeneric
                | PlannedTypeReferenceArity::InvalidGeneric { .. } => {
                    self.issue_type_reference_arity_diagnostic(
                        node,
                        symbol,
                        reference.arity,
                        None,
                    )?;
                    self.error_type()?
                }
            }
        };
        if let Some(cached) = cached_resolved_type {
            return if cached == resolved_type {
                Ok(cached)
            } else {
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ))
            };
        }
        symbol_links.resolved_symbol = Some(symbol);
        if !self.store.set_symbol_node_links(node, symbol_links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedSymbol { node, symbol },
            ));
        }
        let mut type_links = self
            .store
            .type_node_links(node)
            .cloned()
            .unwrap_or_default();
        type_links.resolved_type = Some(resolved_type);
        if !self.store.set_type_node_links(node, type_links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        Ok(resolved_type)
    }

    fn execute_generic_alias_instantiation(
        &mut self,
        reference: &PlannedTypeReference,
        declared_type: TypeId,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        let symbol = reference.symbol;
        let metadata = plan.aliases.get(&symbol).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(symbol))
        })?;
        let links = self
            .store
            .type_alias_links(symbol)
            .cloned()
            .unwrap_or_default();
        let Some(type_parameters) = links.type_parameters.clone() else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
            ));
        };
        if type_parameters.len() != metadata.type_parameters.len() || links.instantiations.is_none()
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
            ));
        }

        let alias_identity = if let Some(owner) = reference.alias_owner {
            let owner_plan = plan.aliases.get(&owner).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(owner))
            })?;
            let arguments = owner_plan
                .type_parameters
                .iter()
                .map(|parameter| execute_type_parameter(self.store, parameter.symbol))
                .collect::<Vec<_>>();
            Some((owner, arguments))
        } else {
            None
        };
        let mut provided_arguments = Vec::with_capacity(reference.type_arguments.len());
        for argument in &reference.type_arguments {
            provided_arguments.push(self.execute_type_node(*argument, plan, prepared)?);
        }
        let key =
            self.type_alias_instantiation_key(&provided_arguments, alias_identity.as_ref())?;
        let mut type_arguments = provided_arguments;
        for parameter in metadata.type_parameters.iter().skip(type_arguments.len()) {
            let default_type = parameter.default_type.ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(symbol))
            })?;
            let default_type = self.execute_type_node(default_type, plan, prepared)?;
            let default_type = self.instantiate_direct_alias_type(
                symbol,
                default_type,
                &type_parameters,
                &type_arguments,
            )?;
            type_arguments.push(default_type);
        }
        let instantiation = self.instantiate_direct_alias_type(
            symbol,
            declared_type,
            &type_parameters,
            &type_arguments,
        )?;

        if let Some(cached) = links
            .instantiations
            .as_ref()
            .and_then(|instantiations| instantiations.get(&key))
            .copied()
        {
            if cached != instantiation || self.store.type_payload(cached).is_none() {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
                ));
            }
            return Ok(cached);
        }

        let mut links = self
            .store
            .type_alias_links(symbol)
            .cloned()
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(
                    symbol,
                ))
            })?;
        let instantiations = links.instantiations.as_mut().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(
                symbol,
            ))
        })?;
        if let Some(previous) = instantiations.insert(key, instantiation)
            && previous != instantiation
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
            ));
        }
        if !self.store.set_type_alias_links(symbol, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
            ));
        }
        Ok(instantiation)
    }

    fn instantiate_direct_alias_type(
        &self,
        symbol: SemanticSymbolId,
        type_: TypeId,
        mapped_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) -> Result<TypeId, DeclaredTypeError> {
        self.validate_direct_alias_type(symbol, type_, mapped_parameters)?;
        if matches!(
            self.store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::TypeParameter(_))
        ) && let Some(index) = mapped_parameters
            .iter()
            .position(|parameter| *parameter == type_)
        {
            return type_arguments.get(index).copied().ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingGenericAliasMetadata(symbol))
            });
        }
        Ok(type_)
    }

    fn validate_direct_alias_type(
        &self,
        symbol: SemanticSymbolId,
        type_: TypeId,
        mapped_parameters: &[TypeId],
    ) -> Result<(), DeclaredTypeError> {
        let record = self.store.type_payload(type_).ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(
                symbol,
            ))
        })?;
        match record.data() {
            TypeData::Intrinsic(_)
                if self
                    .store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| type_ == bootstrap.intrinsic_marker_type) =>
            {
                Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                        alias: symbol,
                        declared_type: type_,
                    },
                ))
            }
            TypeData::TypeParameter(_)
            | TypeData::Intrinsic(_)
            | TypeData::Literal(_)
            | TypeData::Interface(_) => Ok(()),
            TypeData::Union(union)
                if !union
                    .union
                    .types
                    .iter()
                    .any(|constituent| mapped_parameters.contains(constituent)) =>
            {
                Ok(())
            }
            _ => Err(type_node_unavailable(
                TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                    alias: symbol,
                    declared_type: type_,
                },
            )),
        }
    }

    fn type_alias_instantiation_key(
        &mut self,
        type_arguments: &[TypeId],
        alias: Option<&(SemanticSymbolId, Vec<TypeId>)>,
    ) -> Result<CacheHashKey, DeclaredTypeError> {
        let alias = if let Some((symbol, arguments)) = alias {
            let global_symbol = self.store.global_symbol_id(*symbol).ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(*symbol))
            })?;
            Some((global_symbol, arguments.as_slice()))
        } else {
            None
        };
        Ok(type_alias_instantiation_cache_key(type_arguments, alias))
    }

    fn issue_type_reference_arity_diagnostic(
        &mut self,
        node: NodeRef,
        symbol: SemanticSymbolId,
        arity: PlannedTypeReferenceArity,
        generic_global_target: Option<TypeId>,
    ) -> Result<(), DeclaredTypeError> {
        let symbol_name = self
            .store
            .symbol(symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            .filter(|name| !name.is_empty())
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::SymbolNotOwned(symbol),
            ))?
            .to_owned();
        let name = if let Some(target) = generic_global_target {
            self.generic_global_type_display_name(node, symbol, target, &symbol_name)?
        } else {
            symbol_name
        };
        let (code, arguments) = match arity {
            PlannedTypeReferenceArity::NotGeneric => (2315, vec![name]),
            PlannedTypeReferenceArity::InvalidGeneric { minimum, maximum }
                if minimum == maximum =>
            {
                (2314, vec![name, minimum.to_string()])
            }
            PlannedTypeReferenceArity::InvalidGeneric { minimum, maximum } => {
                (2707, vec![name, minimum.to_string(), maximum.to_string()])
            }
            PlannedTypeReferenceArity::Valid => return Ok(()),
        };
        self.diagnostics.add(
            Some(node),
            Diagnostic::with_arguments(
                message_by_code(code).expect("generic arity diagnostics are in the catalog"),
                arguments,
            ),
        );
        Ok(())
    }

    fn generic_global_type_display_name(
        &self,
        node: NodeRef,
        symbol: SemanticSymbolId,
        target: TypeId,
        symbol_name: &str,
    ) -> Result<String, DeclaredTypeError> {
        if preflight_generic_global_type_target(self.store, target)
            .map_err(|_| type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)))?
            .is_some()
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        let target_record = self.store.type_payload(target).ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
        })?;
        let TypeData::Interface(interface) = target_record.data() else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        if target_record
            .symbol()
            .and_then(|target_symbol| self.store.get_merged_symbol(target_symbol))
            != Some(symbol)
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        let [parameter] = interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
            })?
        else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        let parameter_symbol = cached_ordinary_type_parameter_owner(self.store, *parameter)
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
            })?;
        let parameter_name = self
            .store
            .symbol(parameter_symbol)
            .and_then(|parameter| parameter.name().as_utf8())
            .filter(|name| !name.is_empty())
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node))
            })?;
        Ok(format!("{symbol_name}<{parameter_name}>"))
    }

    fn error_type(&self) -> Result<TypeId, DeclaredTypeError> {
        self.store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.error_type)
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))
    }

    fn keyword_type(&self, kind: SyntaxKind) -> Result<TypeId, DeclaredTypeError> {
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?;
        Ok(match kind {
            SyntaxKind::AnyKeyword => bootstrap.any_type,
            SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
            SyntaxKind::StringKeyword => bootstrap.string_type,
            SyntaxKind::NumberKeyword => bootstrap.number_type,
            SyntaxKind::BigIntKeyword => bootstrap.bigint_type,
            SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
            SyntaxKind::SymbolKeyword => bootstrap.es_symbol_type,
            SyntaxKind::VoidKeyword => bootstrap.void_type,
            SyntaxKind::UndefinedKeyword => bootstrap.undefined_type,
            SyntaxKind::NullKeyword => bootstrap.null_type,
            SyntaxKind::NeverKeyword => bootstrap.never_type,
            SyntaxKind::ObjectKeyword => bootstrap.non_primitive_type,
            SyntaxKind::IntrinsicKeyword => bootstrap.intrinsic_marker_type,
            _ => unreachable!("keyword_type is called only for supported keyword nodes"),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, Node, NodeArena, NodeData, NodeFlags, NodeId};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags, EscapedName,
    };
    use ts_core::TextRange;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalTypeFormatFlags, DeclaredTypeHostError, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SymbolNodeLinks, TypeAliasLinks, TypeNodeLinks,
        ValueSymbolLinks,
        bootstrap::UnionReduction,
        callables::{
            CallableFamily, StoredSingleCallableValidation, validate_stored_single_callable,
        },
        formatter::type_to_string_with_host_and_flags,
        global_types::initialize_global_library_types,
        links::{ResolvedSignatureState, SignatureLinks},
        production::GlobalMergeCompletion,
        signatures::SignatureFlags,
        source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
        type_records::{LiteralValue, TypeAlias},
        types::{ObjectFlags, TypeFlags},
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    type StoreState = (usize, usize, [usize; 26], usize, usize);
    type LiteralState = (StoreState, usize, usize, usize);
    type UnionState = (LiteralState, usize, usize);

    fn fixture(source: &str) -> Fixture {
        fixture_with(source, CanonicalModuleState::Script, |_| {})
    }

    fn fixture_with_mutation(source: &str, mutate: impl FnOnce(&mut ParseResult)) -> Fixture {
        fixture_with(source, CanonicalModuleState::Script, mutate)
    }

    fn mutate_first_type_argument_list(
        parsed: &mut ParseResult,
        empty: bool,
        has_trailing_comma: bool,
    ) {
        let reference = parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                matches!(
                    &node.data,
                    NodeData::TypeReferenceNode(reference)
                        if reference.type_arguments.is_some()
                )
                .then_some(id)
            })
            .expect("source has a type-argument list");
        let NodeData::TypeReferenceNode(reference) =
            &mut parsed.arena.get_mut(reference).unwrap().data
        else {
            unreachable!()
        };
        let arguments = reference.type_arguments.as_mut().unwrap();
        if empty {
            arguments.nodes.clear();
        }
        arguments.has_trailing_comma = has_trailing_comma;
    }

    fn invalidate_first_type_argument_range(parsed: &mut ParseResult) {
        let reference = parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                matches!(
                    &node.data,
                    NodeData::TypeReferenceNode(reference)
                        if reference.type_arguments.is_some()
                )
                .then_some(id)
            })
            .expect("source has a type-argument list");
        let NodeData::TypeReferenceNode(reference) =
            &mut parsed.arena.get_mut(reference).unwrap().data
        else {
            unreachable!()
        };
        let arguments = reference.type_arguments.as_mut().unwrap();
        arguments.range = TextRange::new(arguments.range.start, arguments.range.start);
    }

    fn fixture_with_module_state(source: &str, module_state: CanonicalModuleState) -> Fixture {
        fixture_with(source, module_state, |_| {})
    }

    fn fixture_with(
        source: &str,
        module_state: CanonicalModuleState,
        mutate: impl FnOnce(&mut ParseResult),
    ) -> Fixture {
        fixture_with_options(
            source,
            module_state,
            IntrinsicBootstrapOptions::default(),
            mutate,
        )
    }

    fn fixture_with_intrinsic(source: &str, intrinsic: IntrinsicBootstrapOptions) -> Fixture {
        fixture_with_options(source, CanonicalModuleState::Script, intrinsic, |_| {})
    }

    fn global_array_fixture(source: &str) -> Fixture {
        fixture(&format!(
            "interface Array<T> {{}} interface ReadonlyArray<T> {{}} {source}"
        ))
    }

    fn fixture_with_options(
        source: &str,
        module_state: CanonicalModuleState,
        intrinsic: IntrinsicBootstrapOptions,
        mutate: impl FnOnce(&mut ParseResult),
    ) -> Fixture {
        let mut parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        mutate(&mut parsed);
        let file = FileId::new(71);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/type-nodes.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store.initialize_intrinsic_bootstrap(intrinsic).unwrap();

        if module_state == CanonicalModuleState::Script {
            let bound = files.get(&file).unwrap();
            let locals = bound.locals(bound.source_file()).unwrap();
            let mut symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
                .collect::<Vec<_>>();
            symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            for (_, symbol) in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }

        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn post_global_host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn identifier_text(arena: &NodeArena, identifier: NodeId) -> Option<&str> {
        let NodeData::Identifier(identifier) = &arena.get(identifier)?.data else {
            return None;
        };
        Some(&identifier.text)
    }

    fn declaration_name<'a>(arena: &'a NodeArena, node: &Node) -> Option<&'a str> {
        let name = match &node.data {
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::TypeParameterDeclaration(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::ImportSpecifier(data) => data.name,
            _ => return None,
        };
        identifier_text(arena, name)
    }

    fn named_node(fixture: &Fixture, kind: SyntaxKind, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind && declaration_name(&fixture.parsed.arena, node) == Some(name))
                    .then_some(id)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} named {name}"));
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn node_symbol(fixture: &Fixture, node: NodeRef) -> SemanticSymbolId {
        fixture
            .files
            .get(&fixture.file)
            .unwrap()
            .symbol(node)
            .unwrap()
    }

    fn named_symbol(fixture: &Fixture, kind: SyntaxKind, name: &str) -> SemanticSymbolId {
        node_symbol(fixture, named_node(fixture, kind, name))
    }

    fn alias_parts(fixture: &Fixture, name: &str) -> (NodeRef, NodeRef, NodeRef) {
        let declaration = named_node(fixture, SyntaxKind::TypeAliasDeclaration, name);
        let NodeData::TypeAliasDeclaration(alias) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        (
            declaration,
            NodeRef::new(declaration.arena, declaration.file, alias.name),
            NodeRef::new(declaration.arena, declaration.file, alias.type_),
        )
    }

    fn function_type_node(fixture: &Fixture, alias: &str) -> NodeRef {
        let declaration = alias_parts(fixture, alias).0;
        let functions = fixture
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                if record.kind != SyntaxKind::FunctionType {
                    return None;
                }
                let mut current = node;
                loop {
                    let parent = fixture.parsed.arena.get(current)?.parent?;
                    if parent == declaration.node {
                        return Some(NodeRef::new(declaration.arena, declaration.file, node));
                    }
                    current = parent;
                }
            })
            .collect::<Vec<_>>();
        let [function] = functions.as_slice() else {
            panic!("type alias {alias} must own exactly one function type")
        };
        *function
    }

    fn function_parameter_nodes(fixture: &Fixture, function: NodeRef) -> Vec<NodeRef> {
        let NodeData::FunctionTypeNode(function_data) =
            &fixture.parsed.arena.get(function.node).unwrap().data
        else {
            unreachable!()
        };
        function_data
            .parameters
            .nodes
            .iter()
            .map(|node| NodeRef::new(function.arena, function.file, *node))
            .collect()
    }

    fn function_return_node(fixture: &Fixture, function: NodeRef) -> NodeRef {
        let NodeData::FunctionTypeNode(function_data) =
            &fixture.parsed.arena.get(function.node).unwrap().data
        else {
            unreachable!()
        };
        NodeRef::new(
            function.arena,
            function.file,
            function_data
                .type_
                .expect("function has a return annotation"),
        )
    }

    fn parameter_type_node(fixture: &Fixture, parameter: NodeRef) -> NodeRef {
        let NodeData::ParameterDeclaration(parameter_data) =
            &fixture.parsed.arena.get(parameter.node).unwrap().data
        else {
            unreachable!()
        };
        NodeRef::new(
            parameter.arena,
            parameter.file,
            parameter_data
                .type_
                .expect("parameter has a type annotation"),
        )
    }

    fn function_signature(store: &CanonicalTypeMapperStore, function: NodeRef) -> SignatureId {
        store
            .signature_links(function)
            .and_then(|links| links.resolved_signature.signature())
            .expect("function has a resolved signature")
    }

    fn alias_type_parameter_default(fixture: &Fixture, name: &str, index: usize) -> NodeRef {
        let declaration = named_node(fixture, SyntaxKind::TypeAliasDeclaration, name);
        let NodeData::TypeAliasDeclaration(alias) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let parameter = alias.type_parameters.as_ref().unwrap().nodes[index];
        let NodeData::TypeParameterDeclaration(parameter) =
            &fixture.parsed.arena.get(parameter).unwrap().data
        else {
            unreachable!()
        };
        NodeRef::new(
            declaration.arena,
            declaration.file,
            parameter
                .default_type
                .expect("type parameter has a default"),
        )
    }

    fn variable_type_node(fixture: &Fixture, name: &str) -> NodeRef {
        let declaration = named_node(fixture, SyntaxKind::VariableDeclaration, name);
        let NodeData::VariableDeclaration(variable) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        NodeRef::new(
            declaration.arena,
            declaration.file,
            variable.type_.expect("variable has a type annotation"),
        )
    }

    fn merge_duplicate_alias_declarations(fixture: &mut Fixture, name: &str) -> SemanticSymbolId {
        let declarations = fixture
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration
                    && declaration_name(&fixture.parsed.arena, record) == Some(name))
                .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .collect::<Vec<_>>();
        assert_eq!(declarations.len(), 2);
        let symbols = declarations
            .iter()
            .map(|declaration| node_symbol(fixture, *declaration))
            .collect::<Vec<_>>();
        let canonical = symbols[0];
        if symbols[1] != canonical {
            fixture
                .store
                .record_merged_symbol(canonical, symbols[1])
                .unwrap();
        }
        let value_declaration = fixture.store.symbol(canonical).unwrap().value_declaration();
        assert!(fixture.store.set_symbol_declarations(
            canonical,
            Some(declarations),
            value_declaration,
        ));
        canonical
    }

    fn store_state(store: &CanonicalTypeMapperStore) -> StoreState {
        (
            store.type_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.type_resolution_len(),
            store.type_resolution_start(),
        )
    }

    fn alias_instantiation_key(
        type_arguments: &[TypeId],
        alias: Option<(u64, &[TypeId])>,
    ) -> CacheHashKey {
        type_alias_instantiation_cache_key(type_arguments, alias)
    }

    fn literal_state(store: &CanonicalTypeMapperStore) -> LiteralState {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store_state(store),
            bootstrap.string_literal_cache_len(),
            bootstrap.number_literal_cache_len(),
            bootstrap.bigint_literal_cache_len(),
        )
    }

    fn union_state(store: &CanonicalTypeMapperStore) -> UnionState {
        (
            literal_state(store),
            store.type_alias_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        )
    }

    fn union_allocation_state(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store.type_len(),
            store.type_alias_len(),
            bootstrap.union_cache_len(),
            bootstrap.union_of_union_cache_len(),
        )
    }

    fn function_store_state(
        store: &CanonicalTypeMapperStore,
    ) -> (StoreState, usize, usize, usize, usize) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store_state(store),
            store.signature_len(),
            store.type_alias_len(),
            bootstrap.union_cache_len(),
            bootstrap.union_of_union_cache_len(),
        )
    }

    fn union_types(store: &CanonicalTypeMapperStore, union: TypeId) -> &[TypeId] {
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("expected union type")
        };
        &data.union.types
    }

    fn union_origin(store: &CanonicalTypeMapperStore, union: TypeId) -> Option<TypeId> {
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("expected union type")
        };
        data.origin
    }

    fn union_alias_symbol(
        store: &CanonicalTypeMapperStore,
        union: TypeId,
    ) -> Option<SemanticSymbolId> {
        let alias = store.type_payload(union)?.alias()?;
        store.type_alias(alias)?.symbol()
    }

    fn alloc_named_union(
        store: &mut CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        types: &[TypeId],
    ) -> TypeId {
        store.literal_union_type(types, Some(symbol)).unwrap()
    }

    fn alloc_forged_named_union(
        store: &mut CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        types: Vec<TypeId>,
    ) -> TypeId {
        let union = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, types)
            .unwrap();
        let alias = store.alloc_type_alias(Some(symbol)).unwrap();
        assert!(store.set_type_alias(union, Some(alias)));
        union
    }

    fn assert_regular_literal(
        store: &CanonicalTypeMapperStore,
        regular: TypeId,
        expected: &LiteralValue,
    ) {
        let TypeData::Literal(regular_data) = store.type_payload(regular).unwrap().data() else {
            panic!("expected regular literal type")
        };
        assert_eq!(&regular_data.value, expected);
        assert_eq!(regular_data.regular_type, regular);
        let fresh = regular_data
            .fresh_type
            .expect("literal query creates freshness");
        assert_ne!(fresh, regular);
        let TypeData::Literal(fresh_data) = store.type_payload(fresh).unwrap().data() else {
            panic!("expected fresh literal type")
        };
        assert_eq!(&fresh_data.value, expected);
        assert_eq!(fresh_data.regular_type, regular);
        assert_eq!(fresh_data.fresh_type, Some(fresh));
    }

    fn query_declared(
        fixture: &mut Fixture,
        symbol: SemanticSymbolId,
        options: CanonicalTypeQueryOptions,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(&mut fixture.store, &host, options, diagnostics)?
            .get_declared_type_of_symbol(symbol)
    }

    fn query_node(
        fixture: &mut Fixture,
        node: NodeRef,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_type_from_type_node(node)
    }

    fn query_signature_return(
        fixture: &mut Fixture,
        signature: SignatureId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_return_type_of_signature(signature)
    }

    fn query_source_callable(
        fixture: &mut Fixture,
        declaration: NodeRef,
        owner: SemanticSymbolId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_type_of_source_callable(declaration, owner)
    }

    fn query_global_signature_return(
        fixture: &mut Fixture,
        global_types: &CanonicalGlobalTypes,
        signature: SignatureId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new_with_global_types(
            &mut fixture.store,
            &host,
            global_types,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_return_type_of_signature(signature)
    }

    fn canonical_array_target(fixture: &mut Fixture) -> TypeId {
        let symbol = named_symbol(fixture, SyntaxKind::InterfaceDeclaration, "Array");
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap()
    }

    fn query_array_node(
        fixture: &mut Fixture,
        array_type: TypeId,
        node: NodeRef,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new_with_array_type_for_test(
            &mut fixture.store,
            &host,
            array_type,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_type_from_type_node(node)
    }

    fn initialize_fixture_global_types(fixture: &mut Fixture) -> CanonicalGlobalTypes {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        initialize_global_library_types(&mut fixture.store, &host, globals, false).unwrap()
    }

    fn query_global_node(
        fixture: &mut Fixture,
        global_types: &CanonicalGlobalTypes,
        node: NodeRef,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new_with_global_types(
            &mut fixture.store,
            &host,
            global_types,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_type_from_type_node(node)
    }

    fn query_global_declared(
        fixture: &mut Fixture,
        global_types: &CanonicalGlobalTypes,
        symbol: SemanticSymbolId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new_with_global_types(
            &mut fixture.store,
            &host,
            global_types,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_declared_type_of_symbol(symbol)
    }

    fn query_empty_host_declared(
        fixture: &mut Fixture,
        symbol: SemanticSymbolId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_declared_type_of_symbol(symbol)
    }

    fn query_empty_host_global_declared(
        fixture: &mut Fixture,
        global_types: &CanonicalGlobalTypes,
        symbol: SemanticSymbolId,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        CanonicalTypeQuery::new_with_global_types(
            &mut fixture.store,
            &host,
            global_types,
            CanonicalTypeQueryOptions::default(),
            diagnostics,
        )?
        .get_declared_type_of_symbol(symbol)
    }

    fn array_element_node(fixture: &Fixture, array: NodeRef) -> NodeRef {
        let NodeData::ArrayTypeNode(array_data) =
            &fixture.parsed.arena.get(array.node).unwrap().data
        else {
            panic!("expected an array type node")
        };
        NodeRef::new(array.arena, array.file, array_data.element_type)
    }

    fn type_reference_argument_node(
        fixture: &Fixture,
        reference: NodeRef,
        index: usize,
    ) -> NodeRef {
        let NodeData::TypeReferenceNode(reference_data) =
            &fixture.parsed.arena.get(reference.node).unwrap().data
        else {
            panic!("expected a type-reference node")
        };
        NodeRef::new(
            reference.arena,
            reference.file,
            reference_data.type_arguments.as_ref().unwrap().nodes[index],
        )
    }

    fn type_reference_arguments(store: &CanonicalTypeMapperStore, reference: TypeId) -> &[TypeId] {
        let TypeData::TypeReference(reference) = store.type_payload(reference).unwrap().data()
        else {
            panic!("expected a canonical type reference")
        };
        reference.resolved_type_arguments.as_deref().unwrap()
    }

    fn assert_invalid_literal_query_is_atomic(fixture: &mut Fixture) {
        let alias = named_symbol(fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let before = literal_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidLiteralType(_)
            ))
        ));
        assert_eq!(literal_state(&fixture.store), before);
        assert!(fixture.store.type_alias_links(alias).is_none());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn keyword_and_parenthesized_nodes_reuse_exact_bootstrap_identities() {
        let source = concat!(
            "type Any = any; type Unknown = unknown; type String = string; ",
            "type Number = number; type BigInt = bigint; type Boolean = boolean; ",
            "type Symbol = symbol; type Void = void; type Undefined = undefined; ",
            "type Null = null; type Never = never; type Object = object; ",
            "type Intrinsic = intrinsic; type Parenthesized = ((string));",
        );
        let mut fixture = fixture(source);
        let expected = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            [
                ("Any", bootstrap.any_type),
                ("Unknown", bootstrap.unknown_type),
                ("String", bootstrap.string_type),
                ("Number", bootstrap.number_type),
                ("BigInt", bootstrap.bigint_type),
                ("Boolean", bootstrap.boolean_type),
                ("Symbol", bootstrap.es_symbol_type),
                ("Void", bootstrap.void_type),
                ("Undefined", bootstrap.undefined_type),
                ("Null", bootstrap.null_type),
                ("Never", bootstrap.never_type),
                ("Object", bootstrap.non_primitive_type),
                ("Intrinsic", bootstrap.intrinsic_marker_type),
                ("Parenthesized", bootstrap.string_type),
            ]
        };
        let nodes = expected
            .iter()
            .map(|(name, expected)| (alias_parts(&fixture, name).2, *expected))
            .collect::<Vec<_>>();
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut query = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        for (node, expected) in nodes {
            assert_eq!(query.get_type_from_type_node(node), Ok(expected));
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One identity matrix shares a single checker cache.
    fn non_null_literal_nodes_use_regular_interned_identities_and_exact_fresh_links() {
        let source = concat!(
            "type Single = 'shared'; type Template = `shared`; ",
            "type Thousand = 1_000; type ThousandAgain = 1000; ",
            "type Zero = 0; type NegativeZero = -0; ",
            "type PositiveBig = 123_456n; type PositiveBigAgain = 123456n; ",
            "type NegativeBig = -123_456n; type ZeroBig = 0n; type NegativeZeroBig = -0n; ",
            "type True = true; type False = false; type NullLiteral = null;",
        );
        let mut fixture = fixture(source);
        let names = [
            "Single",
            "Template",
            "Thousand",
            "ThousandAgain",
            "NegativeZero",
            "Zero",
            "NegativeBig",
            "PositiveBig",
            "PositiveBigAgain",
            "ZeroBig",
            "NegativeZeroBig",
            "True",
            "False",
            "NullLiteral",
        ];
        let nodes = names
            .iter()
            .map(|name| (*name, alias_parts(&fixture, name).2))
            .collect::<Vec<_>>();
        let (zero, zero_bigint, regular_true, regular_false, null) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.zero_type,
                bootstrap.zero_bigint_type,
                bootstrap.regular_true_type,
                bootstrap.regular_false_type,
                bootstrap.null_type,
            )
        };
        let before = literal_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut resolved = BTreeMap::new();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            for (name, node) in &nodes {
                resolved.insert(*name, query.get_type_from_type_node(*node).unwrap());
            }
        }

        assert_eq!(resolved["Single"], resolved["Template"]);
        assert_eq!(resolved["Thousand"], resolved["ThousandAgain"]);
        assert_eq!(resolved["Zero"], zero);
        assert_eq!(resolved["NegativeZero"], zero);
        assert_eq!(resolved["PositiveBig"], resolved["PositiveBigAgain"]);
        assert_ne!(resolved["PositiveBig"], resolved["NegativeBig"]);
        assert_eq!(resolved["ZeroBig"], zero_bigint);
        assert_eq!(resolved["NegativeZeroBig"], zero_bigint);
        assert_eq!(resolved["True"], regular_true);
        assert_eq!(resolved["False"], regular_false);
        assert_eq!(resolved["NullLiteral"], null);

        assert_regular_literal(
            &fixture.store,
            resolved["Single"],
            &LiteralValue::String("shared".into()),
        );
        assert_regular_literal(
            &fixture.store,
            resolved["Thousand"],
            &LiteralValue::Number(Number::new(1000.0)),
        );
        assert_regular_literal(
            &fixture.store,
            zero,
            &LiteralValue::Number(Number::new(0.0)),
        );
        assert_regular_literal(
            &fixture.store,
            resolved["PositiveBig"],
            &LiteralValue::BigInt(PseudoBigInt::parse_valid("123456n")),
        );
        assert_regular_literal(
            &fixture.store,
            resolved["NegativeBig"],
            &LiteralValue::BigInt(PseudoBigInt::parse_valid("-123456n")),
        );
        assert_regular_literal(
            &fixture.store,
            zero_bigint,
            &LiteralValue::BigInt(PseudoBigInt::default()),
        );

        let after = literal_state(&fixture.store);
        assert_eq!(after.0.0, before.0.0 + 10);
        assert_eq!(after.1, before.1 + 1);
        assert_eq!(after.2, before.2 + 1);
        assert_eq!(after.3, before.3 + 2);
        let null_node = alias_parts(&fixture, "NullLiteral").2;
        assert!(fixture.store.type_node_links(null_node).is_none());
        for (name, node) in &nodes {
            if *name != "NullLiteral" {
                assert_eq!(
                    fixture
                        .store
                        .type_node_links(*node)
                        .and_then(|links| links.resolved_type),
                    Some(resolved[*name])
                );
            }
        }

        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            for (name, node) in &nodes {
                assert_eq!(query.get_type_from_type_node(*node), Ok(resolved[*name]));
            }
        }
        assert_eq!(literal_state(&fixture.store), after);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unary_minus_evaluates_and_interns_the_positive_operand_before_the_result() {
        let mut bigint = fixture("type Negative = -42n;");
        let node = alias_parts(&bigint, "Negative").2;
        let symbol = named_symbol(&bigint, SyntaxKind::TypeAliasDeclaration, "Negative");
        let before = literal_state(&bigint.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let resolved = {
            let host = post_global_host(
                &bigint.parsed.arena,
                bigint.files.get(&bigint.file).unwrap(),
            );
            CanonicalTypeQuery::new(
                &mut bigint.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol)
            .unwrap()
        };
        let after = literal_state(&bigint.store);
        assert_eq!(after.0.0, before.0.0 + 4);
        assert_eq!(after.3, before.3 + 2);
        let positive = bigint
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_bigint_literal_type(&PseudoBigInt::parse_valid("42n"))
            .unwrap();
        let negative = bigint
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_bigint_literal_type(&PseudoBigInt::parse_valid("-42n"))
            .unwrap();
        assert_eq!(resolved, negative);
        assert_eq!(
            bigint
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(negative)
        );
        assert_eq!(
            bigint
                .store
                .type_alias_links(symbol)
                .and_then(|links| links.declared_type),
            Some(negative)
        );
        assert_ne!(positive, negative);
        assert_regular_literal(
            &bigint.store,
            positive,
            &LiteralValue::BigInt(PseudoBigInt::parse_valid("42n")),
        );
        assert_regular_literal(
            &bigint.store,
            negative,
            &LiteralValue::BigInt(PseudoBigInt::parse_valid("-42n")),
        );
        assert!(diagnostics.is_empty());

        let mut negative_zero = fixture("type NegativeZero = -0;");
        let node = alias_parts(&negative_zero, "NegativeZero").2;
        let symbol = named_symbol(
            &negative_zero,
            SyntaxKind::TypeAliasDeclaration,
            "NegativeZero",
        );
        let zero = negative_zero.store.intrinsic_bootstrap().unwrap().zero_type;
        let before = literal_state(&negative_zero.store);
        let resolved = {
            let host = post_global_host(
                &negative_zero.parsed.arena,
                negative_zero.files.get(&negative_zero.file).unwrap(),
            );
            CanonicalTypeQuery::new(
                &mut negative_zero.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol)
            .unwrap()
        };
        let after = literal_state(&negative_zero.store);
        assert_eq!(resolved, zero);
        assert_eq!(
            negative_zero
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(zero)
        );
        assert_eq!(after.0.0, before.0.0 + 1);
        assert_eq!(after.2, before.2);
        assert_regular_literal(
            &negative_zero.store,
            zero,
            &LiteralValue::Number(Number::new(0.0)),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn literal_spelling_variants_normalize_to_the_same_canonical_values() {
        let mut fixture = fixture(concat!(
            r#"type Escaped = "\x61"; type Plain = 'a'; type Template = `a`; "#,
            "type Hex = 0xff; type Decimal = 255; type Binary = 0b1010; type Ten = 10; ",
            "type Octal = 0o10; type Eight = 8; type Exponent = 1.5e2; type OneFifty = 150; ",
            "type HexBig = 0xffn; type DecimalBig = 255n; ",
            "type SeparatedBig = 1_000n; type ThousandBig = 1000n;",
        ));
        let names = [
            "Escaped",
            "Plain",
            "Template",
            "Hex",
            "Decimal",
            "Binary",
            "Ten",
            "Octal",
            "Eight",
            "Exponent",
            "OneFifty",
            "HexBig",
            "DecimalBig",
            "SeparatedBig",
            "ThousandBig",
        ];
        let nodes = names
            .iter()
            .map(|name| (*name, alias_parts(&fixture, name).2))
            .collect::<Vec<_>>();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut resolved = BTreeMap::new();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            for (name, node) in nodes {
                resolved.insert(name, query.get_type_from_type_node(node).unwrap());
            }
        }
        assert_eq!(resolved["Escaped"], resolved["Plain"]);
        assert_eq!(resolved["Plain"], resolved["Template"]);
        for (left, right) in [
            ("Hex", "Decimal"),
            ("Binary", "Ten"),
            ("Octal", "Eight"),
            ("Exponent", "OneFifty"),
            ("HexBig", "DecimalBig"),
            ("SeparatedBig", "ThousandBig"),
        ] {
            assert_eq!(resolved[left], resolved[right], "{left} versus {right}");
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn parsed_unions_sort_deduplicate_cache_and_preserve_direct_alias_identity() {
        let mut fixture = fixture(concat!(
            "type Named = string | number; ",
            "type Duplicate = number | string | string; ",
            "declare let first: string | number; ",
            "declare let second: number | string;",
        ));
        let named_alias_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Named");
        let named_node = alias_parts(&fixture, "Named").2;
        let duplicate_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Duplicate");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let direct = query_node(&mut fixture, named_node, &mut diagnostics).unwrap();
        let declared = query_declared(
            &mut fixture,
            named_alias_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(direct, declared);
        assert_eq!(
            union_alias_symbol(&fixture.store, direct),
            Some(named_alias_symbol)
        );
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            union_types(&fixture.store, direct),
            [bootstrap.string_type, bootstrap.number_type]
        );
        assert!(
            fixture
                .store
                .type_payload(direct)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::PRIMITIVE_UNION)
        );

        let duplicate = query_declared(
            &mut fixture,
            duplicate_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_ne!(duplicate, direct);
        assert_eq!(
            union_types(&fixture.store, duplicate),
            union_types(&fixture.store, direct)
        );
        assert_eq!(
            union_alias_symbol(&fixture.store, duplicate),
            Some(duplicate_symbol)
        );

        let anonymous =
            fixture
                .parsed
                .arena
                .iter()
                .filter_map(|(id, node)| {
                    (node.kind == SyntaxKind::UnionType
                        && node.parent.is_some_and(|parent| {
                            fixture.parsed.arena.get(parent).is_some_and(|parent| {
                                parent.kind == SyntaxKind::VariableDeclaration
                            })
                        }))
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        id,
                    ))
                })
                .collect::<Vec<_>>();
        assert_eq!(anonymous.len(), 2);
        let first = query_node(&mut fixture, anonymous[0], &mut diagnostics).unwrap();
        let second = query_node(&mut fixture, anonymous[1], &mut diagnostics).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            first,
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
        assert_eq!(
            query_node(&mut fixture, named_node, &mut diagnostics),
            Ok(direct)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn exported_union_alias_uses_the_canonical_export_owner_in_both_query_orders() {
        for direct_first in [true, false] {
            let mut fixture = fixture_with_module_state(
                "export type Exported = string | number;",
                CanonicalModuleState::External,
            );
            let (declaration, _, rhs) = alias_parts(&fixture, "Exported");
            let (export, local) = {
                let bound = fixture.files.get(&fixture.file).unwrap();
                (
                    bound.symbol(declaration).unwrap(),
                    bound.local_symbol(declaration).unwrap(),
                )
            };
            let export = fixture.store.get_merged_symbol(export).unwrap();
            assert_ne!(export, local);
            assert_eq!(
                fixture.store.symbol(local).unwrap().export_symbol(),
                Some(export)
            );
            assert!(
                fixture
                    .store
                    .symbol(export)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::TYPE_ALIAS)
            );

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let (direct, declared) = if direct_first {
                let direct = query_node(&mut fixture, rhs, &mut diagnostics).unwrap();
                let declared = query_declared(
                    &mut fixture,
                    export,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap();
                (direct, declared)
            } else {
                let declared = query_declared(
                    &mut fixture,
                    export,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap();
                let direct = query_node(&mut fixture, rhs, &mut diagnostics).unwrap();
                (direct, declared)
            };
            assert_eq!(direct, declared);
            assert_eq!(union_alias_symbol(&fixture.store, direct), Some(export));
            assert_ne!(union_alias_symbol(&fixture.store, direct), Some(local));
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn literal_base_and_boolean_reductions_match_the_pinned_literal_kernel() {
        let mut fixture = fixture(concat!(
            "type StringBase = string | 'a'; type NumberBase = 1 | number; ",
            "type BigIntBase = 1n | bigint; type NamedBool = true | false; ",
            "type BoolRedundant = boolean | true; declare let anonymousBool: true | false;",
        ));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let aliases = ["StringBase", "NumberBase", "BigIntBase"]
            .map(|name| named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, name));
        let reduced = aliases.map(|alias| {
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
        });
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            reduced,
            [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type
            ]
        );

        let named_bool_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "NamedBool");
        let named_bool = query_declared(
            &mut fixture,
            named_bool_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_ne!(named_bool, bootstrap.boolean_type);
        assert_eq!(
            union_types(&fixture.store, named_bool),
            [bootstrap.regular_false_type, bootstrap.regular_true_type]
        );
        assert_eq!(
            fixture.store.type_payload(named_bool).unwrap().flags(),
            TypeFlags::UNION | TypeFlags::BOOLEAN
        );
        assert_eq!(
            union_alias_symbol(&fixture.store, named_bool),
            Some(named_bool_symbol)
        );

        let redundant_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "BoolRedundant");
        let redundant = query_declared(
            &mut fixture,
            redundant_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(
            union_types(&fixture.store, redundant),
            union_types(&fixture.store, named_bool)
        );
        assert_ne!(redundant, named_bool);

        let anonymous =
            fixture
                .parsed
                .arena
                .iter()
                .find_map(|(id, node)| {
                    (node.kind == SyntaxKind::UnionType
                        && node.parent.is_some_and(|parent| {
                            fixture.parsed.arena.get(parent).is_some_and(|parent| {
                                parent.kind == SyntaxKind::VariableDeclaration
                            })
                        }))
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        id,
                    ))
                })
                .unwrap();
        assert_eq!(
            query_node(&mut fixture, anonymous, &mut diagnostics),
            Ok(fixture.store.intrinsic_bootstrap().unwrap().boolean_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn strict_and_loose_nullable_union_precedence_is_exact() {
        let source = concat!(
            "type Nullable = string | null | undefined; type OnlyNullable = null | undefined; ",
            "type AnyCase = string | any; type UnknownCase = string | unknown; ",
            "type NeverCase = string | never;",
        );
        for strict_null_checks in [false, true] {
            let mut fixture = fixture_with_intrinsic(
                source,
                IntrinsicBootstrapOptions {
                    strict_null_checks,
                    ..IntrinsicBootstrapOptions::default()
                },
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let (nullable, only_nullable, any_case, unknown_case, never_case) = {
                let mut resolve = |name| {
                    let symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, name);
                    query_declared(
                        &mut fixture,
                        symbol,
                        CanonicalTypeQueryOptions::default(),
                        &mut diagnostics,
                    )
                    .unwrap()
                };
                (
                    resolve("Nullable"),
                    resolve("OnlyNullable"),
                    resolve("AnyCase"),
                    resolve("UnknownCase"),
                    resolve("NeverCase"),
                )
            };
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            assert_eq!(any_case, bootstrap.any_type);
            assert_eq!(unknown_case, bootstrap.unknown_type);
            assert_eq!(never_case, bootstrap.string_type);
            if strict_null_checks {
                assert_eq!(
                    union_types(&fixture.store, nullable),
                    [
                        bootstrap.undefined_type,
                        bootstrap.null_type,
                        bootstrap.string_type
                    ]
                );
                assert_eq!(
                    union_types(&fixture.store, only_nullable),
                    [bootstrap.undefined_type, bootstrap.null_type]
                );
            } else {
                assert_eq!(nullable, bootstrap.string_type);
                assert_eq!(only_nullable, bootstrap.null_type);
            }
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn named_union_origins_flatten_exactly_and_anonymous_order_reuses_cache() {
        let mut fixture = fixture(concat!(
            "type A = 'a' | 'b'; type B = A | boolean; ",
            "declare let first: A | boolean; declare let second: boolean | A; ",
            "declare let nested: (A | never) | boolean;",
        ));
        let a_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let b_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "B");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let a = query_declared(
            &mut fixture,
            a_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let b = query_declared(
            &mut fixture,
            b_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(union_alias_symbol(&fixture.store, a), Some(a_symbol));
        assert_eq!(union_alias_symbol(&fixture.store, b), Some(b_symbol));
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let a_types = union_types(&fixture.store, a).to_vec();
        assert_eq!(
            union_types(&fixture.store, b),
            [
                a_types[0],
                a_types[1],
                bootstrap.regular_false_type,
                bootstrap.regular_true_type
            ]
        );
        let b_origin = union_origin(&fixture.store, b).unwrap();
        assert_eq!(
            union_types(&fixture.store, b_origin),
            [bootstrap.regular_false_type, bootstrap.regular_true_type, a]
        );
        assert_eq!(union_alias_symbol(&fixture.store, b_origin), None);

        let anonymous =
            fixture
                .parsed
                .arena
                .iter()
                .filter_map(|(id, node)| {
                    (node.kind == SyntaxKind::UnionType
                        && node.parent.is_some_and(|parent| {
                            fixture.parsed.arena.get(parent).is_some_and(|parent| {
                                parent.kind == SyntaxKind::VariableDeclaration
                            })
                        }))
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        id,
                    ))
                })
                .collect::<Vec<_>>();
        assert_eq!(anonymous.len(), 3);
        let first = query_node(&mut fixture, anonymous[0], &mut diagnostics).unwrap();
        let after_first = union_allocation_state(&fixture.store);
        let second = query_node(&mut fixture, anonymous[1], &mut diagnostics).unwrap();
        assert_eq!(first, second);
        assert_eq!(union_allocation_state(&fixture.store), after_first);

        let nested = query_node(&mut fixture, anonymous[2], &mut diagnostics).unwrap();
        assert_eq!(first, nested);
        let after_nested = union_allocation_state(&fixture.store);
        assert_eq!(after_nested.0, after_first.0);
        assert_eq!(after_nested.1, after_first.1);
        assert_eq!(after_nested.2, after_first.2);
        assert_eq!(after_nested.3, after_first.3 + 1);
        assert_ne!(first, b);
        assert_eq!(union_alias_symbol(&fixture.store, first), None);
        assert!(union_origin(&fixture.store, first).is_some());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn repeated_named_origin_cache_hits_do_not_allocate_or_grow_either_union_cache() {
        let mut fixture = fixture(concat!(
            "type A = 'a' | 'b'; ",
            "declare let first: A | boolean | symbol; ",
            "declare let second: symbol | boolean | A;",
        ));
        let a = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut fixture,
            a,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let unions =
            fixture
                .parsed
                .arena
                .iter()
                .filter_map(|(id, node)| {
                    (node.kind == SyntaxKind::UnionType
                        && node.parent.is_some_and(|parent| {
                            fixture.parsed.arena.get(parent).is_some_and(|parent| {
                                parent.kind == SyntaxKind::VariableDeclaration
                            })
                        }))
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        id,
                    ))
                })
                .collect::<Vec<_>>();
        assert_eq!(unions.len(), 2);

        let first = query_node(&mut fixture, unions[0], &mut diagnostics).unwrap();
        assert!(union_origin(&fixture.store, first).is_some());
        let after_first = union_allocation_state(&fixture.store);
        let second = query_node(&mut fixture, unions[1], &mut diagnostics).unwrap();
        assert_eq!(second, first);
        assert_eq!(union_allocation_state(&fixture.store), after_first);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_union_literal_rejects_a_broken_regular_backlink_before_writes_and_retries() {
        let mut fixture = fixture("type Seed = never; type Result = string | Seed;");
        let seed = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Seed");
        let result = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Result");
        let regular = fixture
            .store
            .regular_number_literal_type(Number::new(42.0))
            .unwrap();
        let TypeData::Literal(data) = fixture.store.type_payload(regular).unwrap().data() else {
            panic!("expected regular number literal")
        };
        let fresh = data.fresh_type.unwrap();
        assert!(fixture.store.set_literal_links(regular, None, regular));
        assert!(fixture.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(fresh),
                ..TypeAliasLinks::default()
            }
        ));

        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedLiteralType(fresh)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());

        assert!(
            fixture
                .store
                .set_literal_links(regular, Some(fresh), regular)
        );
        assert!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn literal_preflight_rejects_symbol_bearing_cached_regular_before_query_writes() {
        let mut fixture = fixture("type Bad = 0 | 1;");
        let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let zero = fixture.store.intrinsic_bootstrap().unwrap().zero_type;
        assert!(fixture.store.set_type_symbol(zero, Some(bad)));
        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedLiteralType(zero)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
        let TypeData::Literal(zero_data) = fixture.store.type_payload(zero).unwrap().data() else {
            panic!("zeroType must remain a literal")
        };
        assert_eq!(zero_data.fresh_type, None);
    }

    #[test]
    fn cached_alias_union_requires_its_exact_alias_owner_before_writes_and_retries() {
        let mut fixture = fixture("type Seed = string | number; type Result = Seed | boolean;");
        let seed = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Seed");
        let result = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Result");
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let wrong_owner =
            alloc_named_union(&mut fixture.store, result, &[string_type, number_type]);
        let repaired = alloc_named_union(&mut fixture.store, seed, &[string_type, number_type]);
        assert!(fixture.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(wrong_owner),
                ..TypeAliasLinks::default()
            }
        ));

        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(wrong_owner)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());

        assert!(fixture.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(repaired),
                ..TypeAliasLinks::default()
            }
        ));
        assert!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn named_union_alias_chains_have_identical_warm_and_cold_results() {
        for warm in [false, true] {
            let mut fixture = fixture("type A = 1 | 2; type B = A; type C = B | 3;");
            let a = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
            let b = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "B");
            let c = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "C");
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            if warm {
                query_declared(
                    &mut fixture,
                    a,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap();
                query_declared(
                    &mut fixture,
                    b,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap();
            }
            let result = query_declared(
                &mut fixture,
                c,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            assert_eq!(union_alias_symbol(&fixture.store, result), Some(c));
            let values = union_types(&fixture.store, result)
                .iter()
                .map(|type_| {
                    let TypeData::Literal(data) =
                        fixture.store.type_payload(*type_).unwrap().data()
                    else {
                        panic!("expected a numeric literal")
                    };
                    let LiteralValue::Number(value) = &data.value else {
                        panic!("expected a numeric literal")
                    };
                    value.value()
                })
                .collect::<Vec<_>>();
            assert_eq!(values, [1.0, 2.0, 3.0]);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn valid_cached_union_root_skips_its_unsupported_ast_children_without_writes() {
        let mut fixture = fixture("type Cached = 123 | { value: number };");
        let cached_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Cached");
        let rhs = alias_parts(&fixture, "Cached").2;
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let cached = alloc_named_union(
            &mut fixture.store,
            cached_symbol,
            &[string_type, number_type],
        );
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(cached),
                ..TypeNodeLinks::default()
            }
        ));
        assert_eq!(
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_number_literal_type(Number::new(123.0)),
            None
        );

        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(query_node(&mut fixture, rhs, &mut diagnostics), Ok(cached));
        assert_eq!(union_state(&fixture.store), before);
        assert_eq!(
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_number_literal_type(Number::new(123.0)),
            None
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn malformed_cached_union_root_fails_before_writes_and_accepts_a_repaired_identity() {
        let mut fixture = fixture("type Cached = string | number;");
        let cached_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Cached");
        let rhs = alias_parts(&fixture, "Cached").2;
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let malformed = alloc_forged_named_union(
            &mut fixture.store,
            cached_symbol,
            vec![string_type, number_type],
        );
        assert!(fixture.store.add_type_flags(malformed, TypeFlags::BOOLEAN));
        let repaired = alloc_named_union(
            &mut fixture.store,
            cached_symbol,
            &[string_type, number_type],
        );
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(malformed),
                ..TypeNodeLinks::default()
            }
        ));

        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(malformed)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());

        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(repaired),
                ..TypeNodeLinks::default()
            }
        ));
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Ok(repaired)
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn forged_intrinsic_union_root_and_alias_cache_fail_before_writes_and_retry() {
        let mut root = fixture("type Root = string | number;");
        let root_symbol = named_symbol(&root, SyntaxKind::TypeAliasDeclaration, "Root");
        let root_rhs = alias_parts(&root, "Root").2;
        let (string_type, number_type) = {
            let bootstrap = root.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let forged = root
            .store
            .alloc_intrinsic_type_ex(TypeFlags::STRING, "string", ObjectFlags::NONE)
            .unwrap();
        assert!(root.store.set_type_node_links(
            root_rhs,
            TypeNodeLinks {
                resolved_type: Some(forged),
                ..TypeNodeLinks::default()
            }
        ));
        let before = union_state(&root.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut root, root_rhs, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(forged)
            ))
        );
        assert_eq!(union_state(&root.store), before);
        let repaired = alloc_named_union(&mut root.store, root_symbol, &[string_type, number_type]);
        assert!(root.store.set_type_node_links(
            root_rhs,
            TypeNodeLinks {
                resolved_type: Some(repaired),
                ..TypeNodeLinks::default()
            }
        ));
        assert_eq!(
            query_node(&mut root, root_rhs, &mut diagnostics),
            Ok(repaired)
        );

        let mut alias = fixture("type Seed = never; type Result = string | Seed;");
        let seed = named_symbol(&alias, SyntaxKind::TypeAliasDeclaration, "Seed");
        let result = named_symbol(&alias, SyntaxKind::TypeAliasDeclaration, "Result");
        let (never_type, forged) = {
            let never_type = alias.store.intrinsic_bootstrap().unwrap().never_type;
            let forged = alias
                .store
                .alloc_intrinsic_type_ex(TypeFlags::NEVER, "never", ObjectFlags::NONE)
                .unwrap();
            (never_type, forged)
        };
        assert!(alias.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(forged),
                ..TypeAliasLinks::default()
            }
        ));
        let before = union_state(&alias.store);
        assert_eq!(
            query_declared(
                &mut alias,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(forged)
            ))
        );
        assert_eq!(union_state(&alias.store), before);
        assert!(alias.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(never_type),
                ..TypeAliasLinks::default()
            }
        ));
        assert!(
            query_declared(
                &mut alias,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn forged_literal_pair_and_uncached_union_identity_are_rejected_at_cached_roots() {
        let mut fixture = fixture("type Root = string | number;");
        let root = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Root");
        let rhs = alias_parts(&fixture, "Root").2;
        let regular = fixture
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("forged".into()),
                crate::semantic::type_records::RegularLiteralLink::SelfType,
            )
            .unwrap();
        let fresh = fixture
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("forged".into()),
                crate::semantic::type_records::RegularLiteralLink::Type(regular),
            )
            .unwrap();
        assert!(
            fixture
                .store
                .set_literal_links(regular, Some(fresh), regular)
        );
        assert!(fixture.store.set_literal_links(fresh, Some(fresh), regular));
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(regular),
                ..TypeNodeLinks::default()
            }
        ));
        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedLiteralType(regular)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);

        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let fabricated = fixture.store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Fabricated"),
            CheckFlags::NONE,
        );
        let fabricated_owner =
            alloc_named_union(&mut fixture.store, fabricated, &[string_type, number_type]);
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(fabricated_owner),
                ..TypeNodeLinks::default()
            }
        ));
        let before = union_state(&fixture.store);
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(fabricated_owner)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);

        let forged =
            alloc_forged_named_union(&mut fixture.store, root, vec![string_type, number_type]);
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(forged),
                ..TypeNodeLinks::default()
            }
        ));
        let before = union_state(&fixture.store);
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(forged)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);

        let repaired = alloc_named_union(&mut fixture.store, root, &[string_type, number_type]);
        assert!(fixture.store.set_type_node_links(
            rhs,
            TypeNodeLinks {
                resolved_type: Some(repaired),
                ..TypeNodeLinks::default()
            }
        ));
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Ok(repaired)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_alias_rhs_shape_distinguishes_reference_identity_from_nonunion_syntax() {
        let mut fixture = fixture(concat!(
            "type A = string | number; type B = A; ",
            "type Result = B | boolean; type Plain = string;",
        ));
        let a = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let b = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "B");
        let result = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Result");
        let plain = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Plain");
        let reference = alias_parts(&fixture, "B").2;
        let (string_type, number_type, bigint_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
            )
        };
        let correct = alloc_named_union(&mut fixture.store, a, &[string_type, number_type]);
        let wrong = alloc_named_union(&mut fixture.store, a, &[string_type, bigint_type]);
        assert!(fixture.store.set_type_alias_links(
            a,
            TypeAliasLinks {
                declared_type: Some(correct),
                ..TypeAliasLinks::default()
            }
        ));
        assert!(fixture.store.set_type_node_links(
            reference,
            TypeNodeLinks {
                resolved_type: Some(correct),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(a),
            }
        ));
        assert!(fixture.store.set_type_alias_links(
            b,
            TypeAliasLinks {
                declared_type: Some(wrong),
                ..TypeAliasLinks::default()
            }
        ));
        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(b)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(fixture.store.set_type_alias_links(
            b,
            TypeAliasLinks {
                declared_type: Some(correct),
                ..TypeAliasLinks::default()
            }
        ));
        assert!(
            query_declared(
                &mut fixture,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );

        let forged_plain =
            alloc_named_union(&mut fixture.store, plain, &[string_type, number_type]);
        assert!(fixture.store.set_type_alias_links(
            plain,
            TypeAliasLinks {
                declared_type: Some(forged_plain),
                ..TypeAliasLinks::default()
            }
        ));
        let before = union_state(&fixture.store);
        assert_eq!(
            query_declared(
                &mut fixture,
                plain,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(forged_plain)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(fixture.store.set_type_alias_links(
            plain,
            TypeAliasLinks {
                declared_type: Some(string_type),
                ..TypeAliasLinks::default()
            }
        ));
        assert_eq!(
            query_declared(
                &mut fixture,
                plain,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_alias_cycle_accepts_only_the_canonical_error_result() {
        let source = "type A = B; type B = A; type Result = A | number;";
        let mut cold = fixture(source);
        let cold_result = named_symbol(&cold, SyntaxKind::TypeAliasDeclaration, "Result");
        let cold_error = cold.store.intrinsic_bootstrap().unwrap().error_type;
        let mut cold_diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut cold,
                cold_result,
                CanonicalTypeQueryOptions::default(),
                &mut cold_diagnostics,
            ),
            Ok(cold_error)
        );
        assert_eq!(cold_diagnostics.len(), 2);
        assert!(
            cold_diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2456)
        );

        let mut warm = fixture(source);
        let a = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "A");
        let b = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "B");
        let result = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "Result");
        let a_reference = alias_parts(&warm, "A").2;
        let b_reference = alias_parts(&warm, "B").2;
        let string_type = warm.store.intrinsic_bootstrap().unwrap().string_type;
        for (alias, reference, target) in [(a, a_reference, b), (b, b_reference, a)] {
            assert!(warm.store.set_type_alias_links(
                alias,
                TypeAliasLinks {
                    declared_type: Some(string_type),
                    ..TypeAliasLinks::default()
                }
            ));
            assert!(warm.store.set_type_node_links(
                reference,
                TypeNodeLinks {
                    resolved_type: Some(string_type),
                    ..TypeNodeLinks::default()
                }
            ));
            assert!(warm.store.set_symbol_node_links(
                reference,
                SymbolNodeLinks {
                    resolved_symbol: Some(target),
                }
            ));
        }
        let before = union_state(&warm.store);
        let mut warm_diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut warm,
                result,
                CanonicalTypeQueryOptions::default(),
                &mut warm_diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(a)
            ))
        );
        assert_eq!(union_state(&warm.store), before);
        assert!(warm_diagnostics.is_empty());
    }

    #[test]
    fn trusted_union_queries_skip_global_scans_and_dirty_state_scans_once() {
        let mut fixture = fixture("type Many = (1 | 2) | (3 | 4) | 5;");
        assert!(
            fixture
                .parsed
                .arena
                .iter()
                .filter(|(_, node)| node.kind == SyntaxKind::UnionType)
                .count()
                > 1
        );
        let many = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Many");
        let before = fixture.store.union_cache_validation_scan_count();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            query_declared(
                &mut fixture,
                many,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );
        assert_eq!(fixture.store.union_cache_validation_scan_count(), before);
        fixture.store.mark_union_cache_validation_dirty();
        fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 1, 0)
            .unwrap();
        assert_eq!(
            fixture.store.union_cache_validation_scan_count(),
            before + 1
        );
        fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 1, 0)
            .unwrap();
        assert_eq!(
            fixture.store.union_cache_validation_scan_count(),
            before + 1
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn wildcard_error_and_unknown_precedence_accept_exact_cached_alias_inputs() {
        let mut fixture = fixture(concat!(
            "type Wild = never; type Err = never; ",
            "type WildResult = string | Wild | Err; type ErrorResult = string | Err;",
        ));
        let wild = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Wild");
        let error = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Err");
        let (wildcard_type, error_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.wildcard_type, bootstrap.error_type)
        };
        assert!(fixture.store.set_type_alias_links(
            wild,
            TypeAliasLinks {
                declared_type: Some(wildcard_type),
                ..TypeAliasLinks::default()
            }
        ));
        assert!(fixture.store.set_type_alias_links(
            error,
            TypeAliasLinks {
                declared_type: Some(error_type),
                ..TypeAliasLinks::default()
            }
        ));
        let wild_result = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "WildResult");
        let error_result = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ErrorResult");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                wild_result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(wildcard_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                error_result,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unsupported_union_closures_and_capacity_fail_atomically_and_retry() {
        let mut unsupported = fixture("type Obj = { value: number }; type Bad = 1 | Obj;");
        let bad = named_symbol(&unsupported, SyntaxKind::TypeAliasDeclaration, "Bad");
        let before = union_state(&unsupported.store);
        for _ in 0..2 {
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(matches!(
                query_declared(
                    &mut unsupported,
                    bad,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedUnionConstituent(_)
                ))
            ));
            assert_eq!(union_state(&unsupported.store), before);
            assert!(diagnostics.is_empty());
        }

        assert_eq!(
            unsupported
                .store
                .prepare_type_query_types(&[], &[], &[], usize::MAX, 0),
            Err(LiteralTypeCacheError::Capacity)
        );
        assert_eq!(union_state(&unsupported.store), before);

        let mut cached = fixture("class C {} type Seed = never; type Bad = 1 | Seed;");
        let class = named_symbol(&cached, SyntaxKind::ClassDeclaration, "C");
        let seed = named_symbol(&cached, SyntaxKind::TypeAliasDeclaration, "Seed");
        let bad = named_symbol(&cached, SyntaxKind::TypeAliasDeclaration, "Bad");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let class_type = query_declared(
            &mut cached,
            class,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert!(cached.store.set_type_alias_links(
            seed,
            TypeAliasLinks {
                declared_type: Some(class_type),
                ..TypeAliasLinks::default()
            }
        ));
        let before = union_state(&cached.store);
        assert_eq!(
            query_declared(
                &mut cached,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(class_type)
            ))
        );
        assert_eq!(union_state(&cached.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn recursive_union_aliases_cache_error_and_issue_cycle_diagnostics_once() {
        let mut fixture = fixture("type Recursive = Recursive | string;");
        let recursive = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Recursive");
        let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                recursive,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error)
        );
        let after_first = union_state(&fixture.store);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
        assert_eq!(
            query_declared(
                &mut fixture,
                recursive,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error)
        );
        assert_eq!(union_state(&fixture.store), after_first);
        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn alias_chains_cache_in_type_alias_links_and_ignore_declared_type_links() {
        let mut fixture = fixture("type Base = string; type Alias = Base;");
        let base = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Base");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Alias");
        let (_, _, reference) = alias_parts(&fixture, "Alias");
        let number_type = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_declared_type_links(
            alias,
            DeclaredTypeLinks {
                declared_type: Some(number_type),
                ..DeclaredTypeLinks::default()
            },
        ));

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(base)
                .and_then(|links| links.declared_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(alias)
                .and_then(|links| links.declared_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(alias)
                .and_then(|links| links.declared_type),
            Some(number_type)
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(base)
        );

        let empty = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        let mut retry_diagnostics = CanonicalCheckerDiagnostics::default();
        let mut retry = CanonicalTypeQuery::new(
            &mut fixture.store,
            &empty,
            CanonicalTypeQueryOptions::default(),
            &mut retry_diagnostics,
        )
        .unwrap();
        assert_eq!(retry.get_declared_type_of_symbol(alias), Ok(string_type));
        assert!(retry_diagnostics.is_empty());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_seeds_its_identity_instantiation_in_parameter_order() {
        let mut fixture = fixture("type Id<T, U> = T;");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declared = query_declared(
            &mut fixture,
            alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let links = fixture.store.type_alias_links(alias).unwrap();
        let parameters = links.type_parameters.as_deref().unwrap();
        assert_eq!(parameters.len(), 2);
        let names = parameters
            .iter()
            .map(|parameter| {
                let symbol = fixture
                    .store
                    .type_payload(*parameter)
                    .unwrap()
                    .symbol()
                    .unwrap();
                fixture
                    .store
                    .symbol(symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["T", "U"]);
        assert_eq!(declared, parameters[0]);
        assert_eq!(
            links
                .instantiations
                .as_ref()
                .unwrap()
                .get(&type_list_key(parameters)),
            Some(&declared)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_generic_aliases_substitute_nested_primitive_and_union_arguments() {
        let mut fixture = fixture(concat!(
            "type Id<T> = T; ",
            "type Wrap<T> = Id<T>; ",
            "type Text = Wrap<string>; ",
            "type TextAgain = Wrap<string>; ",
            "type Word = Wrap<'ok'>; ",
            "type Scalar = Wrap<string | number>; ",
            "let standalone: Id<string>;",
        ));
        let id = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let wrap = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Wrap");
        let text = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Text");
        let text_again = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "TextAgain");
        let word = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Word");
        let scalar = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Scalar");
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                text,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                text_again,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        let word_type = query_declared(
            &mut fixture,
            word,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert!(matches!(
            fixture.store.type_payload(word_type).map(TypeRecord::data),
            Some(TypeData::Literal(data))
                if data.value == LiteralValue::String("ok".to_owned())
        ));
        let scalar_type = query_declared(
            &mut fixture,
            scalar,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(
            union_types(&fixture.store, scalar_type),
            [string_type, number_type]
        );

        let standalone = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                let NodeData::TypeReferenceNode(reference) = &node.data else {
                    return None;
                };
                let parent = node
                    .parent
                    .and_then(|parent| fixture.parsed.arena.get(parent))?;
                let NodeData::Identifier(name) =
                    &fixture.parsed.arena.get(reference.type_name)?.data
                else {
                    return None;
                };
                (parent.kind == SyntaxKind::VariableDeclaration && name.text == "Id")
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, id))
            })
            .expect("standalone generic type reference is present");
        assert_eq!(
            query_node(&mut fixture, standalone, &mut diagnostics),
            Ok(string_type)
        );

        let id_links = fixture.store.type_alias_links(id).unwrap();
        assert_eq!(id_links.type_parameters.as_ref().unwrap().len(), 1);
        assert_eq!(id_links.instantiations.as_ref().unwrap().len(), 3);
        let standalone_key = alias_instantiation_key(&[string_type], None);
        assert_eq!(
            id_links
                .instantiations
                .as_ref()
                .unwrap()
                .get(&standalone_key),
            Some(&string_type)
        );
        let text_global = fixture.store.global_symbol_id(text).unwrap();
        let text_again_global = fixture.store.global_symbol_id(text_again).unwrap();
        let text_key = alias_instantiation_key(&[string_type], Some((text_global, &[])));
        let text_again_key =
            alias_instantiation_key(&[string_type], Some((text_again_global, &[])));
        assert_ne!(text_key, text_again_key);
        let wrap_links = fixture.store.type_alias_links(wrap).unwrap();
        assert_eq!(wrap_links.type_parameters.as_ref().unwrap().len(), 1);
        // The two `string` uses retain distinct direct-alias cache keys, as in
        // pinned `getTypeAliasInstantiationKey`.
        assert_eq!(wrap_links.instantiations.as_ref().unwrap().len(), 5);
        assert_eq!(
            wrap_links.instantiations.as_ref().unwrap().get(&text_key),
            Some(&string_type)
        );
        assert_eq!(
            wrap_links
                .instantiations
                .as_ref()
                .unwrap()
                .get(&text_again_key),
            Some(&string_type)
        );

        let after_first_queries = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                text,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                text_again,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                word,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(word_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                scalar,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(scalar_type)
        );
        assert_eq!(
            query_node(&mut fixture, standalone, &mut diagnostics),
            Ok(string_type)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            after_first_queries
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cold_alias_rhs_query_uses_the_same_owner_key_as_declared_query() {
        let mut fixture = fixture("type Id<T> = T; type Text = Id<string>;");
        let id = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let text = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Text");
        let rhs = alias_parts(&fixture, "Text").2;
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Ok(string_type)
        );
        let text_global = fixture.store.global_symbol_id(text).unwrap();
        let owner_key = alias_instantiation_key(&[string_type], Some((text_global, &[])));
        let no_owner_key = alias_instantiation_key(&[string_type], None);
        let instantiations = fixture
            .store
            .type_alias_links(id)
            .unwrap()
            .instantiations
            .as_ref()
            .unwrap();
        assert_eq!(instantiations.get(&owner_key), Some(&string_type));
        assert!(!instantiations.contains_key(&no_owner_key));

        assert_eq!(
            query_declared(
                &mut fixture,
                text,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        let state = union_state(&fixture.store);
        assert_eq!(
            query_node(&mut fixture, rhs, &mut diagnostics),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                text,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(union_state(&fixture.store), state);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_defaults_map_earlier_parameters_and_cache_provided_arity() {
        let mut fixture = fixture(concat!(
            "type Pick<T, U = T> = U; ",
            "type Picked = Pick<string>; ",
            "type Value<T = number> = T; ",
            "type Defaulted = Value;",
        ));
        let pick = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Pick");
        let picked = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Picked");
        let value = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Value");
        let defaulted = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Defaulted");
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                picked,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                defaulted,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(number_type)
        );
        assert_eq!(fixture.store.mapper_len(), 0);
        assert_eq!(
            fixture
                .store
                .type_alias_links(pick)
                .unwrap()
                .instantiations
                .as_ref()
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(value)
                .unwrap()
                .instantiations
                .as_ref()
                .unwrap()
                .len(),
            2
        );

        let mapper_count = fixture.store.mapper_len();
        assert_eq!(
            query_declared(
                &mut fixture,
                picked,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                defaulted,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(number_type)
        );
        assert_eq!(fixture.store.mapper_len(), mapper_count);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_cache_rejects_swapped_parameter_order_before_query_writes() {
        let mut fixture = fixture("type Pair<T, U> = T; let value: Pair<string, number>;");
        let pair = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Pair");
        let reference = variable_type_node(&fixture, "value");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declared = query_declared(
            &mut fixture,
            pair,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let mut links = fixture.store.type_alias_links(pair).unwrap().clone();
        let parameters = links.type_parameters.as_mut().unwrap();
        parameters.swap(0, 1);
        links.instantiations = Some(HashMap::from([(type_list_key(parameters), declared)]));
        assert!(fixture.store.set_type_alias_links(pair, links));
        let before = union_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                query_node(&mut fixture, reference, &mut diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(pair)
                ))
            );
            assert_eq!(union_state(&fixture.store), before);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_cache_rejects_missing_metadata_outside_a_proven_cycle() {
        let mut fixture = fixture("type Id<T> = T; let value: Id<string>;");
        let id = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let reference = variable_type_node(&fixture, "value");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut fixture,
            id,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let mut links = fixture.store.type_alias_links(id).unwrap().clone();
        links.type_parameters = None;
        links.instantiations = None;
        assert!(fixture.store.set_type_alias_links(id, links));
        let before = union_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                query_node(&mut fixture, reference, &mut diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(id)
                ))
            );
            assert_eq!(union_state(&fixture.store), before);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_cache_does_not_borrow_a_downstream_cycle_proof() {
        let mut fixture = fixture("type Cycle = Cycle; type Root<T> = Cycle;");
        let root = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Root");
        let (_, cycle_name, _) = alias_parts(&fixture, "Cycle");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                root,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(root)
                .unwrap()
                .type_parameters
                .as_ref()
                .map(Vec::len),
            Some(1)
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
        assert_eq!(diagnostics.as_slice()[0].node, Some(cycle_name));
        assert_eq!(diagnostics.as_slice()[0].diagnostic.arguments, ["Cycle"]);

        let mut links = fixture.store.type_alias_links(root).unwrap().clone();
        links.type_parameters = None;
        links.instantiations = None;
        assert!(fixture.store.set_type_alias_links(root, links));
        let before = union_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    root,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(root)
                ))
            );
            assert_eq!(union_state(&fixture.store), before);
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
            assert_eq!(diagnostics.as_slice()[0].node, Some(cycle_name));
        }
    }

    #[test]
    fn generic_alias_cache_rejects_poisoned_instantiation_before_query_writes() {
        let mut fixture = fixture("type Id<T> = T; let value: Id<string>;");
        let id = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let reference = variable_type_node(&fixture, "value");
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut fixture,
            id,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let mut links = fixture.store.type_alias_links(id).unwrap().clone();
        links
            .instantiations
            .as_mut()
            .unwrap()
            .insert(alias_instantiation_key(&[string_type], None), number_type);
        assert!(fixture.store.set_type_alias_links(id, links));
        let before = union_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                query_node(&mut fixture, reference, &mut diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(id)
                ))
            );
            assert_eq!(union_state(&fixture.store), before);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_alias_chain_requires_the_exact_rhs_instantiation_key() {
        let mut fixture = fixture("type Id<T> = T; type Root = Id<string>;");
        let id = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let root = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Root");
        let (string_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let root_global = fixture.store.global_symbol_id(root).unwrap();
        let string_key = alias_instantiation_key(&[string_type], Some((root_global, &[])));
        let number_key = alias_instantiation_key(&[number_type], Some((root_global, &[])));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                root,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        let links = fixture.store.type_alias_links(id).unwrap();
        let parameters = links.type_parameters.as_ref().unwrap();
        let identity_key = type_list_key(parameters);
        assert_eq!(
            links.instantiations.as_ref().unwrap().get(&string_key),
            Some(&string_type)
        );
        assert_eq!(
            links.instantiations.as_ref().unwrap().get(&identity_key),
            links.declared_type.as_ref()
        );

        let warm = union_state(&fixture.store);
        assert_eq!(
            query_declared(
                &mut fixture,
                root,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(union_state(&fixture.store), warm);

        let mut links = fixture.store.type_alias_links(id).unwrap().clone();
        let declared_type = links.declared_type;
        let instantiations = links.instantiations.as_mut().unwrap();
        assert_eq!(instantiations.remove(&string_key), Some(string_type));
        assert_eq!(instantiations.insert(number_key, string_type), None);
        assert_eq!(instantiations.get(&identity_key), declared_type.as_ref());
        assert!(fixture.store.set_type_alias_links(id, links));
        let poisoned = union_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    root,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(root)
                ))
            );
            assert_eq!(union_state(&fixture.store), poisoned);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn multi_declaration_aliases_fail_typed_in_cold_and_warm_queries() {
        let mut cold = fixture("type A<T> = T; type A<U> = U;");
        let cold_alias = merge_duplicate_alias_declarations(&mut cold, "A");
        let cold_before = union_state(&cold.store);
        let mut cold_diagnostics = CanonicalCheckerDiagnostics::default();
        for _ in 0..2 {
            assert_eq!(
                query_declared(
                    &mut cold,
                    cold_alias,
                    CanonicalTypeQueryOptions::default(),
                    &mut cold_diagnostics,
                ),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasSymbol(cold_alias)
                ))
            );
            assert_eq!(union_state(&cold.store), cold_before);
        }
        assert!(cold_diagnostics.is_empty());

        let mut warm = fixture("type A<T> = T; type B<U> = U;");
        let warm_alias = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "A");
        let other = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "B");
        let mut warm_diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut warm,
            warm_alias,
            CanonicalTypeQueryOptions::default(),
            &mut warm_diagnostics,
        )
        .unwrap();
        warm.store.record_merged_symbol(warm_alias, other).unwrap();
        let declarations = [warm_alias, other]
            .iter()
            .map(|symbol| warm.store.symbol(*symbol).unwrap().declarations().unwrap()[0])
            .collect::<Vec<_>>();
        let value_declaration = warm.store.symbol(warm_alias).unwrap().value_declaration();
        assert!(warm.store.set_symbol_declarations(
            warm_alias,
            Some(declarations),
            value_declaration,
        ));
        let warm_before = union_state(&warm.store);
        for _ in 0..2 {
            assert_eq!(
                query_declared(
                    &mut warm,
                    warm_alias,
                    CanonicalTypeQueryOptions::default(),
                    &mut warm_diagnostics,
                ),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(warm_alias)
                ))
            );
            assert_eq!(union_state(&warm.store), warm_before);
        }
        assert!(warm_diagnostics.is_empty());
    }

    #[test]
    fn unsupported_later_generic_default_fails_before_query_writes() {
        let mut fixture = fixture("type Bad<T = string, U = intrinsic> = U; let value: Bad;");
        let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let reference = variable_type_node(&fixture, "value");
        let marker = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .intrinsic_marker_type;
        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for _ in 0..2 {
            assert_eq!(
                query_node(&mut fixture, reference, &mut diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                        alias: bad,
                        declared_type: marker,
                    }
                ))
            );
            assert_eq!(union_state(&fixture.store), before);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_defaults_accept_outer_lexical_type_parameters() {
        let mut fixture = fixture("function f<X>() { type Id<T = X> = T; let value: Id; }");
        let outer = named_symbol(&fixture, SyntaxKind::TypeParameter, "X");
        let reference = variable_type_node(&fixture, "value");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let expected = query_declared(
            &mut fixture,
            outer,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

        assert_eq!(
            query_node(&mut fixture, reference, &mut diagnostics),
            Ok(expected)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_arity_errors_match_pinned_diagnostics_and_are_idempotent() {
        let mut fixture = fixture(concat!(
            "type Id<T> = T; ",
            "type Optional<T = string, U = number> = U; ",
            "type Plain = string; ",
            "type Missing = Id; ",
            "type Range = Optional<string, number, boolean>; ",
            "type NotGeneric = Plain<string>;",
        ));
        let missing = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Missing");
        let range = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Range");
        let not_generic = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "NotGeneric");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for symbol in [missing, range, not_generic] {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    symbol,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Ok(error_type)
            );
        }
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| (
                    diagnostic.diagnostic.code(),
                    diagnostic.diagnostic.arguments.clone(),
                ))
                .collect::<Vec<_>>(),
            [
                (2314, vec!["Id".to_owned(), "1".to_owned()]),
                (
                    2707,
                    vec!["Optional".to_owned(), "0".to_owned(), "2".to_owned()],
                ),
                (2315, vec!["Plain".to_owned()]),
            ]
        );
        assert_eq!(
            diagnostics.as_slice()[0].node,
            Some(alias_parts(&fixture, "Missing").2)
        );
        assert_eq!(
            diagnostics.as_slice()[1].node,
            Some(alias_parts(&fixture, "Range").2)
        );
        assert_eq!(
            diagnostics.as_slice()[2].node,
            Some(alias_parts(&fixture, "NotGeneric").2)
        );

        let diagnostic_count = diagnostics.len();
        for symbol in [missing, range, not_generic] {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    symbol,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Ok(error_type)
            );
        }
        assert_eq!(diagnostics.len(), diagnostic_count);
    }

    #[test]
    fn invalid_outer_arity_still_checks_nested_type_arguments_first() {
        let mut fixture = fixture(concat!(
            "type Id<T> = T; ",
            "type Plain = string; ",
            "type Nested = Plain<Id>; ",
            "type Excess = Id<string, Id>;",
        ));
        let nested = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Nested");
        let excess = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Excess");
        let nested_outer = alias_parts(&fixture, "Nested").2;
        let excess_outer = alias_parts(&fixture, "Excess").2;
        let nested_inner = match &fixture.parsed.arena.get(nested_outer.node).unwrap().data {
            NodeData::TypeReferenceNode(reference) => NodeRef::new(
                nested_outer.arena,
                nested_outer.file,
                reference.type_arguments.as_ref().unwrap().nodes[0],
            ),
            _ => unreachable!(),
        };
        let excess_inner = match &fixture.parsed.arena.get(excess_outer.node).unwrap().data {
            NodeData::TypeReferenceNode(reference) => NodeRef::new(
                excess_outer.arena,
                excess_outer.file,
                reference.type_arguments.as_ref().unwrap().nodes[1],
            ),
            _ => unreachable!(),
        };
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                nested,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                excess,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| (diagnostic.diagnostic.code(), diagnostic.node))
                .collect::<Vec<_>>(),
            [
                (2314, Some(nested_inner)),
                (2315, Some(nested_outer)),
                (2314, Some(excess_inner)),
                (2314, Some(excess_outer)),
            ]
        );

        let diagnostic_count = diagnostics.len();
        for symbol in [nested, excess] {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    symbol,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Ok(error_type)
            );
        }
        assert_eq!(diagnostics.len(), diagnostic_count);
    }

    #[test]
    fn cached_forward_generic_default_reference_preserves_cold_atomic_failure() {
        let source = "type Bad<T = U, U = string> = T; let value: Bad;";

        let mut cold = fixture(source);
        let cold_bad = named_symbol(&cold, SyntaxKind::TypeAliasDeclaration, "Bad");
        let cold_u = named_symbol(&cold, SyntaxKind::TypeParameter, "U");
        let cold_default = alias_type_parameter_default(&cold, "Bad", 0);
        let cold_reference = variable_type_node(&cold, "value");
        let cold_before = union_state(&cold.store);
        let mut cold_diagnostics = CanonicalCheckerDiagnostics::default();
        for _ in 0..2 {
            assert_eq!(
                query_node(&mut cold, cold_reference, &mut cold_diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported {
                        alias: cold_bad,
                        default_type: cold_default,
                        referenced_parameter: cold_u,
                    }
                ))
            );
            assert_eq!(union_state(&cold.store), cold_before);
            assert!(cold.store.type_alias_links(cold_bad).is_none());
        }
        assert!(cold_diagnostics.is_empty());

        let mut warm = fixture(source);
        let warm_bad = named_symbol(&warm, SyntaxKind::TypeAliasDeclaration, "Bad");
        let warm_u = named_symbol(&warm, SyntaxKind::TypeParameter, "U");
        let warm_default = alias_type_parameter_default(&warm, "Bad", 0);
        let warm_reference = variable_type_node(&warm, "value");
        let mut warm_diagnostics = CanonicalCheckerDiagnostics::default();
        let warmed_type = query_node(&mut warm, warm_default, &mut warm_diagnostics).unwrap();
        assert_eq!(
            warm.store
                .symbol_node_links(warm_default)
                .and_then(|links| links.resolved_symbol),
            Some(warm_u)
        );
        assert_eq!(
            warm.store
                .type_node_links(warm_default)
                .and_then(|links| links.resolved_type),
            Some(warmed_type)
        );
        assert!(warm.store.type_alias_links(warm_bad).is_none());
        let warm_before = union_state(&warm.store);

        for _ in 0..2 {
            assert_eq!(
                query_node(&mut warm, warm_reference, &mut warm_diagnostics),
                Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported {
                        alias: warm_bad,
                        default_type: warm_default,
                        referenced_parameter: warm_u,
                    }
                ))
            );
            assert_eq!(union_state(&warm.store), warm_before);
            assert!(warm.store.type_alias_links(warm_bad).is_none());
        }
        assert!(warm_diagnostics.is_empty());
    }

    #[test]
    fn circular_generic_alias_defaults_fail_typed_without_recursive_planning() {
        for source in [
            "type A<T = A> = T; let value: A;",
            "type A<T = B> = T; type B<U = A> = U; let value: A;",
        ] {
            let mut fixture = fixture(source);
            let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
            let default_type = alias_type_parameter_default(&fixture, "A", 0);
            let reference = variable_type_node(&fixture, "value");
            let before = union_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            for _ in 0..2 {
                assert_eq!(
                    query_node(&mut fixture, reference, &mut diagnostics),
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::CircularGenericAliasDefault {
                            alias,
                            default_type,
                        }
                    ))
                );
                assert_eq!(union_state(&fixture.store), before);
                assert!(fixture.store.type_alias_links(alias).is_none());
            }
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn unsupported_generic_alias_dependencies_fail_before_semantic_writes() {
        let cases = [
            ("type Maybe<T> = T | null;", 1),
            ("type Constrained<T extends string> = T;", 2),
            ("type Constant<T> = string | number;", 3),
            (
                "type Forward<T = U, U = string> = T; type Bad = Forward;",
                4,
            ),
        ];
        for (source, expected) in cases {
            let mut fixture = fixture(source);
            let alias_name = match expected {
                1 => "Maybe",
                2 => "Constrained",
                3 => "Constant",
                _ => "Bad",
            };
            let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, alias_name);
            let before = union_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let error = query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();
            assert!(
                matches!(
                    (expected, error),
                    (
                        1,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::UnsupportedUnionConstituent(_)
                        )
                    ) | (
                        2,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::GenericAliasConstraintUnsupported { .. }
                        )
                    ) | (
                        3,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::GenericReferenceUnsupported { .. }
                        )
                    ) | (
                        4,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported { .. }
                        )
                    )
                ),
                "unexpected error: {error:?}"
            );
            assert_eq!(union_state(&fixture.store), before);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn malformed_type_argument_lists_fail_typed_before_query_writes() {
        let cases = [
            (
                "type Value<T = string> = T; type Bad = Value<string>;",
                Some((true, false)),
            ),
            (
                "type Plain = string; type Bad = Plain<string>;",
                Some((true, false)),
            ),
            ("type Id<T> = T; type Bad = Id<string,>;", None),
        ];
        for (source, mutation) in cases {
            let mut fixture = if let Some((empty, has_trailing_comma)) = mutation {
                fixture_with_mutation(source, |parsed| {
                    mutate_first_type_argument_list(parsed, empty, has_trailing_comma);
                })
            } else {
                fixture(source)
            };
            let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
            let reference = alias_parts(&fixture, "Bad").2;
            let before = union_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            for _ in 0..2 {
                assert_eq!(
                    query_declared(
                        &mut fixture,
                        bad,
                        CanonicalTypeQueryOptions::default(),
                        &mut diagnostics,
                    ),
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidTypeReference(reference)
                    ))
                );
                assert_eq!(union_state(&fixture.store), before);
            }
            assert!(diagnostics.is_empty());
        }

        let mut fixture = fixture_with_mutation(
            "type Id<T> = T; type Bad = Id<string>;",
            invalidate_first_type_argument_range,
        );
        let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let reference = alias_parts(&fixture, "Bad").2;
        let before = union_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(reference)
            ))
        );
        assert_eq!(union_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn recursive_generic_aliases_match_pinned_arity_and_cycle_diagnostics() {
        let mut fixture = fixture(concat!(
            "type Loop<T> = Loop<T>; ",
            "let explicit: Loop<string>; ",
            "let bare: Loop;",
        ));
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Loop");
        let (_, alias_name, self_reference) = alias_parts(&fixture, "Loop");
        let explicit = variable_type_node(&fixture, "explicit");
        let bare = variable_type_node(&fixture, "bare");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(fixture.store.mapper_len(), 0);
        assert_eq!(fixture.store.type_resolution_len(), 0);
        assert_eq!(fixture.store.type_resolution_start(), 0);
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2315);
        assert_eq!(diagnostics.as_slice()[0].node, Some(self_reference));
        assert_eq!(diagnostics.as_slice()[1].diagnostic.code(), 2456);
        assert_eq!(diagnostics.as_slice()[1].node, Some(alias_name));
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.arguments == ["Loop"])
        );

        assert_eq!(
            query_node(&mut fixture, explicit, &mut diagnostics),
            Ok(error_type)
        );
        assert_eq!(diagnostics.len(), 3);
        assert_eq!(diagnostics.as_slice()[2].diagnostic.code(), 2315);
        assert_eq!(diagnostics.as_slice()[2].node, Some(explicit));
        assert_eq!(
            query_node(&mut fixture, bare, &mut diagnostics),
            Ok(error_type)
        );
        assert_eq!(diagnostics.len(), 3);

        let state = store_state(&fixture.store);
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(
            query_node(&mut fixture, explicit, &mut diagnostics),
            Ok(error_type)
        );
        assert_eq!(
            query_node(&mut fixture, bare, &mut diagnostics),
            Ok(error_type)
        );
        assert_eq!(store_state(&fixture.store), state);
        assert_eq!(diagnostics.len(), 3);
    }

    #[test]
    fn generic_builtin_iterator_return_accepts_its_marker_seed_on_retry() {
        for strict in [false, true] {
            let mut fixture = fixture("type BuiltinIteratorReturn<T> = intrinsic;");
            let alias = named_symbol(
                &fixture,
                SyntaxKind::TypeAliasDeclaration,
                "BuiltinIteratorReturn",
            );
            let (expected, marker) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (
                    if strict {
                        bootstrap.undefined_type
                    } else {
                        bootstrap.any_type
                    },
                    bootstrap.intrinsic_marker_type,
                )
            };
            let options = CanonicalTypeQueryOptions {
                strict_builtin_iterator_return: strict,
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query_declared(&mut fixture, alias, options, &mut diagnostics),
                Ok(expected)
            );
            assert_eq!(
                query_declared(&mut fixture, alias, options, &mut diagnostics),
                Ok(expected)
            );

            let links = fixture.store.type_alias_links(alias).unwrap();
            let parameters = links.type_parameters.as_deref().unwrap();
            assert_eq!(parameters.len(), 1);
            assert_eq!(links.declared_type, Some(expected));
            assert_eq!(
                links
                    .instantiations
                    .as_ref()
                    .unwrap()
                    .get(&type_list_key(parameters)),
                Some(&marker)
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn non_generic_aliases_to_class_and_interface_preserve_origin_identities() {
        let mut fixture = fixture(concat!(
            "class Model {} interface Shape {} ",
            "type ModelAlias = Model; type ShapeAlias = Shape;",
        ));
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Model");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Shape");
        let class_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ModelAlias");
        let interface_alias =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ShapeAlias");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let class_alias_type = query_declared(
            &mut fixture,
            class_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let interface_alias_type = query_declared(
            &mut fixture,
            interface_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let class_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        let interface_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        assert_eq!(class_alias_type, class_type);
        assert_eq!(interface_alias_type, interface_type);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_alias_cycle_uses_the_shared_stack_and_issues_ts2456_once() {
        let mut fixture = fixture("type A = A;");
        let raw_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let alias = fixture.store.get_merged_symbol(raw_alias).unwrap();
        let (_, name, reference) = alias_parts(&fixture, "A");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            assert_eq!(query.get_declared_type_of_symbol(alias), Ok(error_type));
            assert_eq!(query.get_declared_type_of_symbol(alias), Ok(error_type));
        }
        assert!(fixture.store.type_resolution_is_empty());
        let links = fixture.store.type_alias_links(alias).unwrap();
        assert_eq!(links.declared_type, Some(error_type));
        assert!(links.type_parameters.is_none());
        assert!(links.instantiations.is_none());
        assert_eq!(
            fixture
                .store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(error_type)
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].node, Some(name));
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.arguments, ["A"]);
    }

    #[test]
    fn diagnostic_free_convenience_rejects_alias_before_a_real_cycle_query() {
        let mut fixture = fixture("type A = A;");
        let raw_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let alias = fixture.store.get_merged_symbol(raw_alias).unwrap();
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let before = store_state(&fixture.store);
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, alias),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::DiagnosticOwnerRequired(alias)
            ))
        );
        assert_eq!(store_state(&fixture.store), before);
        assert!(fixture.store.type_alias_links(alias).is_none());

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(error_type)
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
    }

    #[test]
    fn mutual_alias_cycle_reports_each_unwound_alias_once_and_caches_error() {
        let mut fixture = fixture("type A = B; type B = A;");
        let a = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let b = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "B");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            assert_eq!(query.get_declared_type_of_symbol(a), Ok(error_type));
            assert_eq!(query.get_declared_type_of_symbol(b), Ok(error_type));
        }
        assert!(fixture.store.type_resolution_is_empty());
        assert_eq!(
            fixture
                .store
                .type_alias_links(a)
                .and_then(|links| links.declared_type),
            Some(error_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(b)
                .and_then(|links| links.declared_type),
            Some(error_type)
        );
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.arguments[0].as_str())
                .collect::<Vec<_>>(),
            ["B", "A"]
        );
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2456)
        );
    }

    #[test]
    fn builtin_iterator_return_uses_the_query_option_and_other_intrinsics_do_not() {
        for (strict, expected_undefined) in [(false, false), (true, true)] {
            let mut fixture = fixture(concat!(
                "type BuiltinIteratorReturn = intrinsic; ",
                "type OtherIntrinsic = intrinsic;",
            ));
            let builtin = named_symbol(
                &fixture,
                SyntaxKind::TypeAliasDeclaration,
                "BuiltinIteratorReturn",
            );
            let other = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "OtherIntrinsic");
            let (expected, marker) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (
                    if expected_undefined {
                        bootstrap.undefined_type
                    } else {
                        bootstrap.any_type
                    },
                    bootstrap.intrinsic_marker_type,
                )
            };
            let options = CanonicalTypeQueryOptions {
                strict_builtin_iterator_return: strict,
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query_declared(&mut fixture, builtin, options, &mut diagnostics),
                Ok(expected)
            );
            assert_eq!(
                query_declared(&mut fixture, other, options, &mut diagnostics),
                Ok(marker)
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn iterator_return_option_is_store_global_for_transitive_aliases_in_both_orders() {
        for (established, requested) in [(false, true), (true, false)] {
            let mut fixture = fixture(concat!(
                "type BuiltinIteratorReturn = intrinsic; ",
                "type Wrapper = BuiltinIteratorReturn;",
            ));
            let wrapper = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Wrapper");
            let expected = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                if established {
                    bootstrap.undefined_type
                } else {
                    bootstrap.any_type
                }
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query_declared(
                    &mut fixture,
                    wrapper,
                    CanonicalTypeQueryOptions {
                        strict_builtin_iterator_return: established,
                    },
                    &mut diagnostics,
                ),
                Ok(expected)
            );
            let before = store_state(&fixture.store);
            assert_eq!(
                query_declared(
                    &mut fixture,
                    wrapper,
                    CanonicalTypeQueryOptions {
                        strict_builtin_iterator_return: requested,
                    },
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::CheckerOptionMismatch {
                        established_strict_builtin_iterator_return: established,
                        requested_strict_builtin_iterator_return: requested,
                    }
                ))
            );
            assert_eq!(store_state(&fixture.store), before);
            assert_eq!(
                fixture
                    .store
                    .type_alias_links(wrapper)
                    .and_then(|links| links.declared_type),
                Some(expected)
            );
            assert_eq!(
                fixture.store.claimed_strict_builtin_iterator_return(),
                Some(established)
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn malformed_alias_merge_error_is_cache_independent_and_atomic() {
        for seeded in [false, true] {
            let mut fixture = fixture("type A = string;");
            let raw = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
            let alias = fixture.store.get_merged_symbol(raw).unwrap();
            assert!(fixture.store.set_symbol_flags(
                alias,
                SymbolFlags::TYPE_ALIAS | SymbolFlags::ALIAS,
                CheckFlags::NONE,
            ));
            if seeded {
                let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
                assert!(fixture.store.set_type_alias_links(
                    alias,
                    TypeAliasLinks {
                        declared_type: Some(string_type),
                        ..TypeAliasLinks::default()
                    },
                ));
            }
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query_declared(
                    &mut fixture,
                    raw,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(alias)
                ))
            );
            assert_eq!(store_state(&fixture.store), before);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn type_and_symbol_node_caches_are_reused_without_name_reresolution() {
        let mut type_cached = fixture("type Base = string; type Alias = Base;");
        let alias = named_symbol(&type_cached, SyntaxKind::TypeAliasDeclaration, "Alias");
        let base = named_symbol(&type_cached, SyntaxKind::TypeAliasDeclaration, "Base");
        let reference = alias_parts(&type_cached, "Alias").2;
        let number_type = type_cached.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(type_cached.store.set_type_node_links(
            reference,
            TypeNodeLinks {
                resolved_type: Some(number_type),
                ..TypeNodeLinks::default()
            },
        ));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut type_cached,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(number_type)
        );
        assert!(type_cached.store.type_alias_links(base).is_none());
        assert!(type_cached.store.symbol_node_links(reference).is_none());

        let mut symbol_cached = fixture("type Base = string; type Alias = Missing;");
        let alias = named_symbol(&symbol_cached, SyntaxKind::TypeAliasDeclaration, "Alias");
        let base = named_symbol(&symbol_cached, SyntaxKind::TypeAliasDeclaration, "Base");
        let reference = alias_parts(&symbol_cached, "Alias").2;
        let string_type = symbol_cached
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        let raw_pre_merge = symbol_cached.store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("RawBase"),
            CheckFlags::NONE,
        );
        assert!(symbol_cached.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(raw_pre_merge),
            },
        ));
        symbol_cached
            .store
            .record_merged_symbol(base, raw_pre_merge)
            .unwrap();
        assert_eq!(
            query_declared(
                &mut symbol_cached,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            symbol_cached
                .store
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(base)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn named_reference_boundaries_are_typed_and_atomic_without_diagnostics() {
        let cases = [
            ("namespace N { export interface X {} } type Bad = N.X;", 0),
            ("type Bad = Missing;", 1),
            ("interface Box<T> {} type Bad = Box<string>;", 2),
            ("class Box<T> {} type Bad = Box;", 3),
        ];

        for (source, expected) in cases {
            let mut fixture = fixture(source);
            let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let error = query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();
            assert!(
                matches!(
                    (expected, error),
                    (
                        0,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::QualifiedTypeReference(_)
                        )
                    ) | (
                        1,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::MissingTypeReference(_)
                        )
                    ) | (
                        2,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::TypeArgumentsUnsupported(_)
                        )
                    ) | (
                        3,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::GenericReferenceUnsupported { .. }
                        )
                    )
                ),
                "unexpected error: {error:?}"
            );
            assert_eq!(store_state(&fixture.store), before);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn import_alias_references_are_typed_and_atomic() {
        let mut fixture = fixture_with_module_state(
            "import { Remote as Local } from 'pkg'; type Bad = Local;",
            CanonicalModuleState::External,
        );
        let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let before = store_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::ImportAliasTypeReference { .. }
            ))
        ));
        assert_eq!(store_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn malformed_literal_payloads_and_operators_fail_before_semantic_writes() {
        let mut malformed_number = fixture_with_mutation("type Bad = 1;", |parsed| {
            let numeric = parsed
                .arena
                .iter()
                .find_map(|(id, node)| (node.kind == SyntaxKind::NumericLiteral).then_some(id))
                .unwrap();
            let NodeData::NumericLiteral(data) = &mut parsed.arena.get_mut(numeric).unwrap().data
            else {
                unreachable!()
            };
            data.text = "not-a-number".into();
        });
        assert_invalid_literal_query_is_atomic(&mut malformed_number);

        let mut invalid_prefix = fixture_with_mutation("type Bad = -1n;", |parsed| {
            let prefix = parsed
                .arena
                .iter()
                .find_map(|(id, node)| {
                    (node.kind == SyntaxKind::PrefixUnaryExpression).then_some(id)
                })
                .unwrap();
            let NodeData::PrefixUnaryExpression(data) =
                &mut parsed.arena.get_mut(prefix).unwrap().data
            else {
                unreachable!()
            };
            data.operator = SyntaxKind::PlusToken;
        });
        assert_invalid_literal_query_is_atomic(&mut invalid_prefix);
    }

    #[test]
    fn invalid_literal_cache_links_are_rejected_atomically_before_alias_execution() {
        let mut fixture = fixture("type Bad = 0;");
        let zero = fixture.store.intrinsic_bootstrap().unwrap().zero_type;
        assert!(fixture.store.set_literal_links(zero, Some(zero), zero));
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let before = literal_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedLiteralType(zero)
            ))
        );
        assert_eq!(literal_state(&fixture.store), before);
        assert!(fixture.store.type_alias_links(alias).is_none());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn every_remaining_deferred_type_node_family_and_recursive_array_fail_atomically() {
        let source = concat!(
            "declare const value: string; ",
            "type ArrayAlias = string[]; type TupleAlias = [string]; ",
            "type IntersectionAlias = object & {}; ",
            "type OperatorAlias = keyof object; type IndexedAlias = { a: string }['a']; ",
            "type MappedAlias<T> = { [K in keyof T]: T[K] }; ",
            "type ConditionalAlias<T> = T extends string ? string : number; ",
            "type InferAlias<T> = T extends infer U ? U : never; ",
            "type ImportTypeAlias = import('pkg').Value; type QueryAlias = typeof value; ",
            "type ThisAlias = this; type RecursiveArray = RecursiveArray[];",
        );
        let aliases = [
            "ArrayAlias",
            "TupleAlias",
            "IntersectionAlias",
            "OperatorAlias",
            "IndexedAlias",
            "MappedAlias",
            "ConditionalAlias",
            "InferAlias",
            "ImportTypeAlias",
            "QueryAlias",
            "ThisAlias",
            "RecursiveArray",
        ];
        let mut fixture = fixture(source);
        for name in aliases {
            let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, name);
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(matches!(
                query_declared(
                    &mut fixture,
                    alias,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax { .. }
                ))
            ));
            assert_eq!(store_state(&fixture.store), before, "alias {name}");
            assert!(diagnostics.is_empty());
            assert!(fixture.store.type_alias_links(alias).is_none());
        }
    }

    #[test]
    fn jsdoc_foreign_and_stale_inputs_fail_before_checker_writes() {
        let mut jsdoc = fixture_with_mutation("type A = string;", |parsed| {
            let body = parsed
                .arena
                .iter()
                .find_map(|(_, node)| {
                    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                        return None;
                    };
                    Some(alias.type_)
                })
                .unwrap();
            parsed.arena.get_mut(body).unwrap().flags = NodeFlags(NODE_FLAG_JSDOC);
        });
        let alias = named_symbol(&jsdoc, SyntaxKind::TypeAliasDeclaration, "A");
        let before = store_state(&jsdoc.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut jsdoc,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::JsDoc(_)
            ))
        ));
        assert_eq!(store_state(&jsdoc.store), before);
        assert!(diagnostics.is_empty());

        let mut local = fixture("type Local = string;");
        let foreign = fixture("type Foreign = string;");
        let foreign_body = alias_parts(&foreign, "Foreign").2;
        let before = store_state(&local.store);
        let host = post_global_host(&local.parsed.arena, local.files.get(&local.file).unwrap());
        {
            let mut query = CanonicalTypeQuery::new(
                &mut local.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap();
            assert!(matches!(
                query.get_type_from_type_node(foreign_body),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::MissingOrForeignFacts(_)
                ))
            ));
        }
        assert_eq!(store_state(&local.store), before);

        let mut stale = fixture("type Stale = string;");
        let before = store_state(&stale.store);
        let orphan = stale
            .parsed
            .arena
            .iter()
            .next()
            .map(|(_, node)| node.clone())
            .unwrap();
        stale.parsed.arena.alloc(orphan);
        assert!(matches!(
            DeclaredTypeHost::new([(&stale.parsed.arena, stale.files.get(&stale.file).unwrap())]),
            Err(DeclaredTypeHostError::ArenaRevisionMismatch { .. })
        ));
        assert_eq!(store_state(&stale.store), before);
    }

    fn canonical_fixture_symbol(
        fixture: &Fixture,
        kind: SyntaxKind,
        name: &str,
    ) -> SemanticSymbolId {
        fixture
            .store
            .get_merged_symbol(named_symbol(fixture, kind, name))
            .unwrap()
    }

    fn property_type_literal_child(fixture: &Fixture, literal: NodeRef, index: usize) -> NodeRef {
        let NodeData::TypeLiteralNode(literal_data) =
            &fixture.parsed.arena.get(literal.node).unwrap().data
        else {
            panic!("expected a type literal")
        };
        let member = literal_data.members.nodes[index];
        let NodeData::PropertyDeclaration(property) =
            &fixture.parsed.arena.get(member).unwrap().data
        else {
            panic!("the parser currently emits property declarations for type members")
        };
        NodeRef::new(
            literal.arena,
            literal.file,
            property.type_.expect("property has an annotation"),
        )
    }

    #[test]
    fn parser_property_members_feed_ordered_type_literal_and_interface_construction() {
        let mut fixture = fixture(concat!(
            "interface Model { readonly id: string; optional?: number; ",
            "nested: { enabled: boolean; leaf: { value: null } } } ",
            "type Shape = { first: string; readonly second?: number; ",
            "nested: { count: bigint } }; ",
            r#"const sample = { field: "value" };"#,
        ));
        let interface_node = named_node(&fixture, SyntaxKind::InterfaceDeclaration, "Model");
        let NodeData::InterfaceDeclaration(interface_data) =
            &fixture.parsed.arena.get(interface_node.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(interface_data.members.nodes.iter().all(|member| {
            fixture.parsed.arena.get(*member).unwrap().kind == SyntaxKind::PropertyDeclaration
        }));
        let (_, _, shape_node) = alias_parts(&fixture, "Shape");
        let NodeData::TypeLiteralNode(shape_data) =
            &fixture.parsed.arena.get(shape_node.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(shape_data.members.nodes.iter().all(|member| {
            fixture.parsed.arena.get(*member).unwrap().kind == SyntaxKind::PropertyDeclaration
        }));
        let object_node = fixture
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

        let model = canonical_fixture_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Model");
        let shape = canonical_fixture_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Shape");
        let (model_plan, shape_plan, object_plan) = {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            (
                object_members::plan_interface(&fixture.store, &host, model).unwrap(),
                object_members::plan_type_literal(&fixture.store, &host, shape_node, Some(shape))
                    .unwrap(),
                object_members::plan_object_literal(&fixture.store, &host, object_node).unwrap(),
            )
        };
        assert_eq!(
            model_plan
                .properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["id", "optional", "nested"]
        );
        assert_eq!(
            shape_plan
                .properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "second", "nested"]
        );
        assert!(!model_plan.properties[0].optional);
        assert!(model_plan.properties[1].optional);
        assert!(shape_plan.properties[1].optional);
        assert_eq!(
            model_plan
                .properties
                .iter()
                .map(|property| property.readonly)
                .collect::<Vec<_>>(),
            [true, false, false]
        );
        assert_eq!(
            shape_plan
                .properties
                .iter()
                .map(|property| property.readonly)
                .collect::<Vec<_>>(),
            [false, true, false]
        );
        assert_eq!(object_plan.properties.len(), 1);
        assert!(!object_plan.properties[0].readonly);
        for plan in [&model_plan, &shape_plan, &object_plan] {
            for property in &plan.properties {
                let name = fixture.parsed.arena.get(property.name_node.node).unwrap();
                let NodeData::Identifier(identifier) = &name.data else {
                    panic!("planned property name must remain an identifier")
                };
                assert_eq!(identifier.text, property.name);
                assert_eq!(name.parent, Some(property.declaration.node));
            }
        }
        let before_rejected_publication = store_state(&fixture.store);
        let (error_type, string_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.string_type)
        };
        assert_eq!(
            object_members::publish_property_members(
                &mut fixture.store,
                &object_plan,
                PropertyObjectState::Shell(error_type),
                &[string_type],
            ),
            Err(PropertyObjectError::InvalidObjectLiteral(object_node))
        );
        assert_eq!(store_state(&fixture.store), before_rejected_publication);
        assert!(
            fixture
                .store
                .value_symbol_links(object_plan.properties[0].symbol)
                .is_none()
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let model_type = query_declared(
            &mut fixture,
            model,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let shape_type = query_declared(
            &mut fixture,
            shape,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert!(diagnostics.is_empty());

        let TypeData::Interface(model_data) =
            fixture.store.type_payload(model_type).unwrap().data()
        else {
            panic!("interface construction must retain interface identity")
        };
        assert_eq!(
            fixture
                .store
                .type_payload(model_type)
                .unwrap()
                .object_flags(),
            ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        );
        let expected_model_properties = model_plan
            .properties
            .iter()
            .map(|property| property.symbol)
            .collect::<Vec<_>>();
        assert_eq!(
            model_data.reference.object.structured.properties.as_deref(),
            Some(expected_model_properties.as_slice())
        );
        let TypeData::Object(shape_data) = fixture.store.type_payload(shape_type).unwrap().data()
        else {
            panic!("type literal aliases construct anonymous object types")
        };
        assert_eq!(
            fixture
                .store
                .type_payload(shape_type)
                .unwrap()
                .object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        let expected_shape_properties = shape_plan
            .properties
            .iter()
            .map(|property| property.symbol)
            .collect::<Vec<_>>();
        assert_eq!(
            shape_data.structured.properties.as_deref(),
            Some(expected_shape_properties.as_slice())
        );
        let alias = fixture
            .store
            .type_payload(shape_type)
            .unwrap()
            .alias()
            .and_then(|alias| fixture.store.type_alias(alias))
            .unwrap();
        assert_eq!(alias.symbol(), Some(shape));
        assert_eq!(alias.type_arguments(), None);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(model_plan.properties[1].symbol)
                .and_then(|links| links.resolved_type),
            Some(fixture.store.intrinsic_bootstrap().unwrap().number_type)
        );
        assert_eq!(
            fixture
                .store
                .symbol(model_plan.properties[0].symbol)
                .unwrap()
                .check_flags(),
            CheckFlags::NONE
        );

        let warm_state = store_state(&fixture.store);
        assert_eq!(
            query_declared(
                &mut fixture,
                model,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(model_type)
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                shape,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(shape_type)
        );
        assert_eq!(store_state(&fixture.store), warm_state);
    }

    #[test]
    fn interface_member_cache_accepts_cold_bases_warm_and_members_warm_states() {
        let mut cold = fixture("interface Model { value: string } let model: Model;");
        let model = canonical_fixture_symbol(&cold, SyntaxKind::InterfaceDeclaration, "Model");
        let reference = variable_type_node(&cold, "model");
        let plan = {
            let host = post_global_host(&cold.parsed.arena, cold.files.get(&cold.file).unwrap());
            object_members::plan_interface(&cold.store, &host, model).unwrap()
        };
        let declared_type = {
            let host = post_global_host(&cold.parsed.arena, cold.files.get(&cold.file).unwrap());
            cold.store
                .get_declared_type_of_symbol(&host, model)
                .unwrap()
        };

        assert_eq!(
            object_members::interface_state(&cold.store, &plan, declared_type),
            Ok(PropertyObjectState::Shell(declared_type)),
            "a cold declared-member shell is valid"
        );
        assert!(
            cold.store
                .publish_interface_no_base_resolution(declared_type)
        );
        assert_eq!(
            object_members::interface_state(&cold.store, &plan, declared_type),
            Ok(PropertyObjectState::Shell(declared_type)),
            "base resolution and declared-member resolution are independent caches"
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut cold, reference, &mut diagnostics),
            Ok(declared_type)
        );
        assert_eq!(
            object_members::interface_state(&cold.store, &plan, declared_type),
            Ok(PropertyObjectState::Resolved(declared_type))
        );
        let TypeData::Interface(interface) = cold.store.type_payload(declared_type).unwrap().data()
        else {
            panic!("interface member publication preserves its declared identity")
        };
        assert!(interface.base_types_resolved);
        assert!(interface.declared_members_resolved);
        let warm_state = store_state(&cold.store);
        assert_eq!(
            query_node(&mut cold, reference, &mut diagnostics),
            Ok(declared_type)
        );
        assert_eq!(store_state(&cold.store), warm_state);
        assert!(diagnostics.is_empty());

        let mut poisoned = fixture("interface Model { value: string } let model: Model;");
        let model = canonical_fixture_symbol(&poisoned, SyntaxKind::InterfaceDeclaration, "Model");
        let reference = variable_type_node(&poisoned, "model");
        let plan = {
            let host = post_global_host(
                &poisoned.parsed.arena,
                poisoned.files.get(&poisoned.file).unwrap(),
            );
            object_members::plan_interface(&poisoned.store, &host, model).unwrap()
        };
        let declared_type = {
            let host = post_global_host(
                &poisoned.parsed.arena,
                poisoned.files.get(&poisoned.file).unwrap(),
            );
            poisoned
                .store
                .get_declared_type_of_symbol(&host, model)
                .unwrap()
        };
        assert!(poisoned.store.set_interface_base_resolution(
            declared_type,
            true,
            None,
            Some(Vec::new()),
        ));
        assert_eq!(
            object_members::interface_state(&poisoned.store, &plan, declared_type),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: model,
                type_: declared_type,
            })
        );
        let poisoned_state = store_state(&poisoned.store);
        assert_eq!(
            query_node(&mut poisoned, reference, &mut diagnostics),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                    symbol: model,
                    declared_type,
                }
            ))
        );
        assert_eq!(store_state(&poisoned.store), poisoned_state);
    }

    #[test]
    fn global_object_interface_value_merge_resolves_the_type_side_only() {
        let source = concat!(
            "interface Object {} ",
            "declare var Object: unknown; ",
            "let value: Object;",
        );
        let mut merged = fixture(source);
        let object = canonical_fixture_symbol(&merged, SyntaxKind::InterfaceDeclaration, "Object");
        let interface_declaration = named_node(&merged, SyntaxKind::InterfaceDeclaration, "Object");
        let value_declaration = named_node(&merged, SyntaxKind::VariableDeclaration, "Object");
        let reference = variable_type_node(&merged, "value");
        let symbol = merged.store.symbol(object).unwrap();
        assert_eq!(
            symbol.flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        );
        assert_eq!(symbol.value_declaration(), Some(value_declaration));
        assert_eq!(
            symbol.declarations(),
            Some([interface_declaration, value_declaration].as_slice())
        );
        let plan = {
            let host = post_global_host(
                &merged.parsed.arena,
                merged.files.get(&merged.file).unwrap(),
            );
            object_members::plan_interface(&merged.store, &host, object).unwrap()
        };
        assert!(plan.properties.is_empty());

        let object_type = {
            let host = post_global_host(
                &merged.parsed.arena,
                merged.files.get(&merged.file).unwrap(),
            );
            merged
                .store
                .get_declared_type_of_symbol(&host, object)
                .unwrap()
        };
        assert!(
            merged
                .store
                .publish_interface_no_base_resolution(object_type)
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut merged, reference, &mut diagnostics),
            Ok(object_type)
        );
        assert_eq!(
            object_members::interface_state(&merged.store, &plan, object_type),
            Ok(PropertyObjectState::Resolved(object_type))
        );
        assert!(diagnostics.is_empty());

        let mut poisoned = fixture(source);
        let object =
            canonical_fixture_symbol(&poisoned, SyntaxKind::InterfaceDeclaration, "Object");
        let declaration = named_node(&poisoned, SyntaxKind::InterfaceDeclaration, "Object");
        assert!(poisoned.store.set_symbol_flags(
            object,
            SymbolFlags::INTERFACE
                | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                | SymbolFlags::VALUE_MODULE,
            CheckFlags::NONE,
        ));
        let before = store_state(&poisoned.store);
        let result = {
            let host = post_global_host(
                &poisoned.parsed.arena,
                poisoned.files.get(&poisoned.file).unwrap(),
            );
            object_members::plan_interface(&poisoned.store, &host, object)
        };
        assert_eq!(
            result,
            Err(PropertyObjectError::InvalidInterface {
                declaration,
                symbol: object,
            })
        );
        assert_eq!(store_state(&poisoned.store), before);
        assert!(
            query_declared(
                &mut poisoned,
                object,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_err()
        );
        assert_eq!(store_state(&poisoned.store), before);
    }

    #[test]
    fn inline_empty_type_literal_reuses_bootstrap_but_aliased_empty_is_distinct() {
        let mut fixture = fixture("let inline: {}; type Empty = {};");
        let inline = variable_type_node(&fixture, "inline");
        let empty = canonical_fixture_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Empty");
        let bootstrap_empty = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .empty_type_literal_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_node(&mut fixture, inline, &mut diagnostics),
            Ok(bootstrap_empty)
        );
        let aliased = query_declared(
            &mut fixture,
            empty,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_ne!(aliased, bootstrap_empty);
        assert_eq!(
            fixture.store.type_payload(aliased).unwrap().object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(
            fixture
                .store
                .type_payload(aliased)
                .unwrap()
                .alias()
                .and_then(|alias| fixture.store.type_alias(alias))
                .and_then(TypeAlias::symbol),
            Some(empty)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn recursive_interfaces_publish_shells_but_recursive_structural_aliases_are_typed_unsupported()
    {
        let mut interfaces = fixture(
            "interface A { b: B; self?: A } interface B { a: A; payload: { ok: boolean } }",
        );
        let a = canonical_fixture_symbol(&interfaces, SyntaxKind::InterfaceDeclaration, "A");
        let b = canonical_fixture_symbol(&interfaces, SyntaxKind::InterfaceDeclaration, "B");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let a_type = query_declared(
            &mut interfaces,
            a,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let b_type = interfaces
            .store
            .declared_type_links(b)
            .and_then(|links| links.declared_type)
            .unwrap();
        assert_ne!(a_type, b_type);
        for (symbol, type_) in [(a, a_type), (b, b_type)] {
            assert_eq!(
                interfaces
                    .store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type),
                Some(type_)
            );
            assert!(
                interfaces
                    .store
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
        }
        assert!(diagnostics.is_empty());

        let mut aliases = fixture("type A = { b: B }; type B = { a: A };");
        let alias_a = canonical_fixture_symbol(&aliases, SyntaxKind::TypeAliasDeclaration, "A");
        let before = store_state(&aliases.store);
        assert!(matches!(
            query_declared(
                &mut aliases,
                alias_a,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::GenericReferenceUnsupported { .. }
            ))
        ));
        assert_eq!(store_state(&aliases.store), before);
        assert!(aliases.store.type_alias_links(alias_a).is_none());
    }

    #[test]
    fn nested_type_literal_poison_leaves_retryable_shell_and_warm_property_poison_is_detected() {
        let mut fixture = fixture("type Outer = { child: { value: string } };");
        let outer = canonical_fixture_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Outer");
        let outer_node = alias_parts(&fixture, "Outer").2;
        let child_node = property_type_literal_child(&fixture, outer_node, 0);
        let poison = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            child_node,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut fixture,
                outer,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidLiteralType(node)
            )) if node == child_node
        ));
        let shell = fixture
            .store
            .type_node_links(outer_node)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture.store.type_payload(shell).unwrap().object_flags(),
            ObjectFlags::ANONYMOUS
        );
        assert!(fixture.store.type_alias_links(outer).is_none());

        assert!(
            fixture
                .store
                .set_type_node_links(child_node, TypeNodeLinks::default())
        );
        let resolved = query_declared(
            &mut fixture,
            outer,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(resolved, shell);
        let property = {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            object_members::plan_type_literal(&fixture.store, &host, outer_node, Some(outer))
                .unwrap()
                .properties[0]
                .clone()
        };
        let expected_child = fixture
            .store
            .type_node_links(child_node)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(poison),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned_state = store_state(&fixture.store);
        assert!(matches!(
            query_declared(
                &mut fixture,
                outer,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidLiteralType(node)
            )) if node == outer_node
        ));
        assert_eq!(store_state(&fixture.store), poisoned_state);
        assert!(fixture.store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(expected_child),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            query_declared(
                &mut fixture,
                outer,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(resolved)
        );
    }

    #[test]
    fn unsupported_property_object_shapes_fail_before_identity_allocation() {
        let cases = [
            (
                "interface Bad { method(): string }",
                SyntaxKind::InterfaceDeclaration,
            ),
            (
                "interface Bad<T> { value: T }",
                SyntaxKind::InterfaceDeclaration,
            ),
            (
                "interface Base {} interface Bad extends Base { value: string }",
                SyntaxKind::InterfaceDeclaration,
            ),
            (
                "type Bad<T> = { value: T };",
                SyntaxKind::TypeAliasDeclaration,
            ),
            (
                "type Bad = { 'value': string };",
                SyntaxKind::TypeAliasDeclaration,
            ),
        ];
        for (source, declaration_kind) in cases {
            let mut fixture = fixture(source);
            let bad = canonical_fixture_symbol(&fixture, declaration_kind, "Bad");
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(
                query_declared(
                    &mut fixture,
                    bad,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .is_err()
            );
            assert_eq!(store_state(&fixture.store), before, "source: {source}");
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn poisoned_interface_payloads_fail_closed_before_identity_allocation() {
        for poison in 0..5 {
            let mut fixture =
                fixture_with_mutation("interface Model { value: string }", |parsed| {
                    let declaration = parsed
                        .arena
                        .iter()
                        .find_map(|(id, node)| {
                            (node.kind == SyntaxKind::InterfaceDeclaration).then_some(id)
                        })
                        .unwrap();
                    let record = parsed.arena.get_mut(declaration).unwrap();
                    if poison == 0 {
                        record.flags = NodeFlags(1);
                    } else {
                        let NodeData::InterfaceDeclaration(interface) = &mut record.data else {
                            unreachable!()
                        };
                        match poison {
                            1 => interface.flow_node = Some(ts_ast::FlowNodeId(1)),
                            2 => interface.local_symbol = Some(ts_ast::SymbolId(1)),
                            3 => interface.symbol = Some(ts_ast::SymbolId(1)),
                            4 => interface.modifiers = Some(ts_ast::ModifierList::default()),
                            _ => unreachable!(),
                        }
                    }
                });
            let model =
                canonical_fixture_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Model");

            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(
                query_declared(
                    &mut fixture,
                    model,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .is_err(),
                "poison case {poison}"
            );
            assert_eq!(store_state(&fixture.store), before, "poison case {poison}");
            assert!(fixture.store.declared_type_links(model).is_none());
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn merged_interface_flags_and_parented_property_object_owners_fail_before_allocation() {
        let mut interface = fixture("interface Model { value: string }");
        let model = canonical_fixture_symbol(&interface, SyntaxKind::InterfaceDeclaration, "Model");
        assert!(interface.store.set_symbol_flags(
            model,
            SymbolFlags::INTERFACE | SymbolFlags::VALUE_MODULE,
            CheckFlags::NONE,
        ));
        let before = store_state(&interface.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            query_declared(
                &mut interface,
                model,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_err()
        );
        assert_eq!(store_state(&interface.store), before);
        assert!(diagnostics.is_empty());

        let mut parented_interface = fixture("interface Model { value: string }");
        let model = canonical_fixture_symbol(
            &parented_interface,
            SyntaxKind::InterfaceDeclaration,
            "Model",
        );
        let declaration = named_node(
            &parented_interface,
            SyntaxKind::InterfaceDeclaration,
            "Model",
        );
        let members = parented_interface.store.symbol(model).unwrap().members();
        let parent = parented_interface
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_symbol;
        assert!(
            parented_interface
                .store
                .symbol(model)
                .unwrap()
                .parent()
                .is_none()
        );
        assert!(parented_interface.store.set_symbol_relationships(
            model,
            members,
            None,
            Some(parent),
            None,
        ));
        let before = store_state(&parented_interface.store);
        let result = {
            let host = post_global_host(
                &parented_interface.parsed.arena,
                parented_interface
                    .files
                    .get(&parented_interface.file)
                    .unwrap(),
            );
            object_members::plan_interface(&parented_interface.store, &host, model)
        };
        assert_eq!(
            result,
            Err(PropertyObjectError::InvalidInterface {
                declaration,
                symbol: model,
            })
        );
        assert_eq!(store_state(&parented_interface.store), before);
        assert!(
            query_declared(
                &mut parented_interface,
                model,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_err()
        );
        assert_eq!(store_state(&parented_interface.store), before);
        assert!(
            parented_interface
                .store
                .declared_type_links(model)
                .is_none()
        );
        assert!(diagnostics.is_empty());

        let mut literal = fixture("type Shape = { value: string };");
        let shape = canonical_fixture_symbol(&literal, SyntaxKind::TypeAliasDeclaration, "Shape");
        let (_, _, type_literal) = alias_parts(&literal, "Shape");
        let owner = literal
            .files
            .get(&literal.file)
            .unwrap()
            .symbol(type_literal)
            .unwrap();
        let members = literal.store.symbol(owner).unwrap().members();
        assert!(literal.store.symbol(owner).unwrap().parent().is_none());
        assert!(
            literal
                .store
                .set_symbol_relationships(owner, members, None, Some(shape), None,)
        );
        let before = store_state(&literal.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            query_declared(
                &mut literal,
                shape,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_err()
        );
        assert_eq!(store_state(&literal.store), before);
        assert!(diagnostics.is_empty());

        let mut alias = fixture("type Shape = { value: string };");
        let shape = canonical_fixture_symbol(&alias, SyntaxKind::TypeAliasDeclaration, "Shape");
        let (_, _, type_literal) = alias_parts(&alias, "Shape");
        assert!(alias.store.set_symbol_flags(
            shape,
            SymbolFlags::TYPE_ALIAS | SymbolFlags::VALUE_MODULE,
            CheckFlags::NONE,
        ));
        let before = store_state(&alias.store);
        let result = {
            let host = post_global_host(&alias.parsed.arena, alias.files.get(&alias.file).unwrap());
            object_members::plan_type_literal(&alias.store, &host, type_literal, Some(shape))
        };
        assert_eq!(
            result,
            Err(PropertyObjectError::InvalidTypeLiteral(type_literal))
        );
        assert_eq!(store_state(&alias.store), before);
    }

    #[test]
    fn warm_interface_reference_validates_properties_and_cached_symbol_identity() {
        let mut fixture = fixture("interface Model { value: string } let model: Model;");
        let model = canonical_fixture_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Model");
        let reference = variable_type_node(&fixture, "model");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let model_type = query_node(&mut fixture, reference, &mut diagnostics).unwrap();
        let property = {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            object_members::plan_interface(&fixture.store, &host, model)
                .unwrap()
                .properties[0]
                .symbol
        };
        let expected = fixture
            .store
            .value_symbol_links(property)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let poison = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(poison),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = store_state(&fixture.store);

        assert!(query_node(&mut fixture, reference, &mut diagnostics).is_err());
        assert_eq!(store_state(&fixture.store), poisoned);

        assert!(fixture.store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(expected),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: None,
            },
        ));
        let missing_symbol = store_state(&fixture.store);
        assert!(matches!(
            query_node(&mut fixture, reference, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedSymbol { node, symbol }
            )) if node == reference && symbol == model
        ));
        assert_eq!(store_state(&fixture.store), missing_symbol);

        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(model),
            },
        ));
        assert_eq!(
            query_node(&mut fixture, reference, &mut diagnostics),
            Ok(model_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One identity/cache/flag transition matrix.
    fn array_type_nodes_share_the_authoritative_target_cache_and_first_allocation_flags() {
        let mut fixture = fixture(
            "interface Array<T> {} \
             let any_values: any[]; let first: number[]; \
             let second: number[]; let nested: number[][];",
        );
        let array_type = canonical_array_target(&mut fixture);
        let (any_type, number_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.any_type, bootstrap.number_type)
        };
        let any_array = create_type_from_generic_global_type(
            &mut fixture.store,
            array_type,
            any_type,
            ObjectFlags::NONE,
        )
        .unwrap();
        assert_eq!(
            fixture
                .store
                .type_payload(any_array)
                .unwrap()
                .object_flags(),
            ObjectFlags::REFERENCE
        );

        let any_node = variable_type_node(&fixture, "any_values");
        let first_node = variable_type_node(&fixture, "first");
        let second_node = variable_type_node(&fixture, "second");
        let nested_node = variable_type_node(&fixture, "nested");
        let nested_element = array_element_node(&fixture, nested_node);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_array_node(&mut fixture, array_type, any_node, &mut diagnostics),
            Ok(any_array)
        );
        let first =
            query_array_node(&mut fixture, array_type, first_node, &mut diagnostics).unwrap();
        let second =
            query_array_node(&mut fixture, array_type, second_node, &mut diagnostics).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            type_reference_arguments(&fixture.store, first),
            [number_type]
        );
        assert_eq!(
            fixture.store.type_payload(first).unwrap().object_flags(),
            ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE
        );
        assert_eq!(
            create_type_from_generic_global_type(
                &mut fixture.store,
                array_type,
                number_type,
                ObjectFlags::NONE,
            ),
            Ok(first)
        );
        assert!(
            fixture
                .store
                .type_payload(first)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );

        let nested =
            query_array_node(&mut fixture, array_type, nested_node, &mut diagnostics).unwrap();
        assert_ne!(nested, first);
        assert_eq!(type_reference_arguments(&fixture.store, nested), [first]);
        assert_eq!(
            fixture
                .store
                .type_node_links(nested_element)
                .and_then(|links| links.resolved_type),
            Some(first)
        );
        let TypeData::TypeReference(nested_reference) =
            fixture.store.type_payload(nested).unwrap().data()
        else {
            panic!("nested array must be a canonical reference")
        };
        assert_eq!(nested_reference.object.target, Some(array_type));

        assert!(fixture.store.set_type_node_links(
            first_node,
            TypeNodeLinks {
                resolved_type: Some(any_array),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(
                &mut fixture,
                array_type,
                first_node,
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(node)
            )) if node == first_node
        ));
        assert_eq!(store_state(&fixture.store), poisoned);
        assert!(fixture.store.set_type_node_links(
            first_node,
            TypeNodeLinks {
                resolved_type: Some(first),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            query_array_node(&mut fixture, array_type, first_node, &mut diagnostics,),
            Ok(first)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn target_only_array_queries_keep_array_union_constituents_fail_closed() {
        let mut fixture = fixture("interface Array<T> {} type U = number[] | string;");
        let array_type = canonical_array_target(&mut fixture);
        let body = alias_parts(&fixture, "U").2;
        let before = store_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert!(matches!(
            query_array_node(&mut fixture, array_type, body, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(_)
            )),
        ));
        assert_eq!(store_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn property_object_array_elements_publish_the_exact_element_identity() {
        let mut fixture = fixture("interface Array<T> {} let values: { id: number }[];");
        let array_type = canonical_array_target(&mut fixture);
        let node = variable_type_node(&fixture, "values");
        let element_node = array_element_node(&fixture, node);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let any_type = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        let poisoned_array = create_type_from_generic_global_type(
            &mut fixture.store,
            array_type,
            any_type,
            ObjectFlags::NONE,
        )
        .unwrap();
        assert!(fixture.store.set_type_node_links(
            node,
            TypeNodeLinks {
                resolved_type: Some(poisoned_array),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), poisoned);
        assert!(fixture.store.type_node_links(element_node).is_none());
        assert!(
            fixture
                .store
                .set_type_node_links(node, TypeNodeLinks::default())
        );

        let resolved = query_array_node(&mut fixture, array_type, node, &mut diagnostics).unwrap();
        let element_type = fixture
            .store
            .type_node_links(element_node)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            type_reference_arguments(&fixture.store, resolved),
            [element_type]
        );
        let TypeData::TypeReference(reference) =
            fixture.store.type_payload(resolved).unwrap().data()
        else {
            panic!("array type syntax must create a reference")
        };
        assert_eq!(reference.object.target, Some(array_type));
        assert!(
            fixture
                .store
                .type_payload(resolved)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );
        let warm = store_state(&fixture.store);
        assert_eq!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Ok(resolved)
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn malformed_array_target_parameters_fail_before_query_writes() {
        let mut fixture = fixture("interface Array<T> {} let values: number[];");
        let array_type = canonical_array_target(&mut fixture);
        let node = variable_type_node(&fixture, "values");
        let number_type = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let (parameter, this_type) = {
            let TypeData::Interface(interface) =
                fixture.store.type_payload(array_type).unwrap().data()
            else {
                panic!("Array must have an interface target")
            };
            (
                interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                interface.this_type.unwrap(),
            )
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert!(fixture.store.set_type_parameter_resolution(
            parameter,
            None,
            Some(number_type),
            None,
            None,
        ));
        let ordinary_poison = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), ordinary_poison);
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(parameter, None, None, None, None)
        );

        assert!(fixture.store.set_type_parameter_resolution(
            this_type,
            Some(array_type),
            Some(number_type),
            None,
            None,
        ));
        let this_poison = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), this_poison);
        assert!(fixture.store.set_type_parameter_resolution(
            this_type,
            Some(array_type),
            None,
            None,
            None,
        ));

        assert!(query_array_node(&mut fixture, array_type, node, &mut diagnostics).is_ok());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn malformed_array_cache_fails_before_writes_and_reuses_repaired_first_identity() {
        let mut fixture = fixture("interface Array<T> {} let values: number[];");
        let array_type = canonical_array_target(&mut fixture);
        let node = variable_type_node(&fixture, "values");
        let target_symbol = fixture.store.type_payload(array_type).unwrap().symbol();
        let (number_type, string_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let forged = fixture
            .store
            .alloc_type_reference(ObjectFlags::NONE, target_symbol)
            .unwrap();
        assert!(
            fixture
                .store
                .set_object_target_and_mapper(forged, Some(array_type), None)
        );
        assert!(
            fixture
                .store
                .set_type_reference_resolution(forged, None, Some(vec![string_type]),)
        );
        assert_eq!(
            fixture.store.insert_object_instantiation(
                array_type,
                type_list_key(&[number_type]),
                forged,
            ),
            Some(forged)
        );

        let poisoned = store_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), poisoned);
        assert!(fixture.store.type_node_links(node).is_none());

        assert!(
            fixture
                .store
                .set_type_reference_resolution(forged, None, Some(vec![number_type]),)
        );
        assert!(fixture.store.set_type_object_flags(
            forged,
            ObjectFlags::REFERENCE | ObjectFlags::ARRAY_LITERAL,
        ));
        let poisoned_flags = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), poisoned_flags);
        assert!(
            fixture
                .store
                .set_type_object_flags(forged, ObjectFlags::REFERENCE)
        );
        assert_eq!(
            query_array_node(&mut fixture, array_type, node, &mut diagnostics),
            Ok(forged)
        );
        assert_eq!(fixture.store.type_len(), poisoned.0);
        assert!(
            !fixture
                .store
                .type_payload(forged)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn absent_or_malformed_global_array_fails_closed_without_resolving_the_element() {
        let mut fixture = fixture("let values: (() => string)[];");
        let node = variable_type_node(&fixture, "values");
        let element = array_element_node(&fixture, node);
        let (empty_generic, empty_object, malformed_target) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.empty_generic_type,
                bootstrap.empty_object_type,
                bootstrap.number_type,
            )
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_node(&mut fixture, node, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: error_node,
                    kind: SyntaxKind::ArrayType,
                }
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), before);

        let before_malformed = store_state(&fixture.store);
        assert!(matches!(
            query_array_node(
                &mut fixture,
                malformed_target,
                node,
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == node
        ));
        assert_eq!(store_state(&fixture.store), before_malformed);

        let type_count = fixture.store.type_len();
        assert_eq!(
            query_array_node(&mut fixture, empty_generic, node, &mut diagnostics,),
            Ok(empty_object)
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.type_node_links(element), None);
        assert_eq!(
            fixture
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(empty_object)
        );
        assert_eq!(
            query_array_node(&mut fixture, empty_generic, node, &mut diagnostics,),
            Ok(empty_object)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_global_array_references_share_shorthand_identity_and_support_nesting() {
        let mut fixture = global_array_fixture(concat!(
            "let shorthand: number[]; ",
            "let direct: Array<number>; ",
            "let readonly: ReadonlyArray<string>; ",
            "let unionElement: Array<string | number>; ",
            "let nested: Array<ReadonlyArray<number[]>>; ",
            "type Maybe = Array<number> | null;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let shorthand = variable_type_node(&fixture, "shorthand");
        let direct = variable_type_node(&fixture, "direct");
        let readonly = variable_type_node(&fixture, "readonly");
        let union_element = variable_type_node(&fixture, "unionElement");
        let nested = variable_type_node(&fixture, "nested");
        let maybe = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Maybe");
        let (number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let shorthand_type =
            query_global_node(&mut fixture, &global_types, shorthand, &mut diagnostics).unwrap();
        assert_eq!(
            query_global_node(&mut fixture, &global_types, direct, &mut diagnostics),
            Ok(shorthand_type),
            "Array<number> and number[] must share the target-local identity",
        );
        assert_eq!(
            type_reference_arguments(&fixture.store, shorthand_type),
            [number]
        );
        assert!(
            fixture
                .store
                .type_payload(shorthand_type)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );

        let readonly_type =
            query_global_node(&mut fixture, &global_types, readonly, &mut diagnostics).unwrap();
        let TypeData::TypeReference(readonly_reference) =
            fixture.store.type_payload(readonly_type).unwrap().data()
        else {
            panic!("ReadonlyArray<string> must be a reference")
        };
        assert_eq!(
            readonly_reference.object.target,
            Some(global_types.readonly_array_type)
        );
        assert_eq!(
            readonly_reference.resolved_type_arguments.as_deref(),
            Some(&[string][..])
        );

        let union_element_type =
            query_global_node(&mut fixture, &global_types, union_element, &mut diagnostics)
                .unwrap();
        let union_element_argument =
            type_reference_arguments(&fixture.store, union_element_type)[0];
        assert_eq!(
            union_types(&fixture.store, union_element_argument),
            [string, number]
        );

        let nested_type =
            query_global_node(&mut fixture, &global_types, nested, &mut diagnostics).unwrap();
        let readonly_number_array = type_reference_arguments(&fixture.store, nested_type)[0];
        let TypeData::TypeReference(readonly_number_reference) = fixture
            .store
            .type_payload(readonly_number_array)
            .unwrap()
            .data()
        else {
            panic!("the nested readonly element must be a reference")
        };
        assert_eq!(
            readonly_number_reference.object.target,
            Some(global_types.readonly_array_type)
        );
        let number_array = readonly_number_reference
            .resolved_type_arguments
            .as_deref()
            .unwrap()[0];
        assert_eq!(
            fixture
                .store
                .canonical_array_reference(&global_types, number_array)
                .unwrap()
                .unwrap()
                .element_type,
            number
        );

        let maybe_type =
            query_global_declared(&mut fixture, &global_types, maybe, &mut diagnostics).unwrap();
        assert_eq!(
            maybe_type, shorthand_type,
            "loose nullish reduction preserves the direct array identity"
        );
        let warm = store_state(&fixture.store);
        assert_eq!(
            query_global_node(&mut fixture, &global_types, direct, &mut diagnostics),
            Ok(shorthand_type)
        );
        assert_eq!(
            query_global_node(&mut fixture, &global_types, readonly, &mut diagnostics),
            Ok(readonly_type)
        );
        assert_eq!(
            query_global_node(&mut fixture, &global_types, union_element, &mut diagnostics,),
            Ok(union_element_type)
        );
        assert_eq!(
            query_global_node(&mut fixture, &global_types, nested, &mut diagnostics),
            Ok(nested_type)
        );
        assert_eq!(
            query_global_declared(&mut fixture, &global_types, maybe, &mut diagnostics),
            Ok(maybe_type)
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_global_array_arity_errors_are_canonical_and_warm_idempotently() {
        let mut fixture = fixture(concat!(
            "interface Array<Element> {} ",
            "interface ReadonlyArray<Item> {} ",
            "let missing: Array; ",
            "let extra: Array<number, string>; ",
            "let readonlyMissing: ReadonlyArray; ",
            "let readonlyExtra: ReadonlyArray<number, string>;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let nodes = [
            variable_type_node(&fixture, "missing"),
            variable_type_node(&fixture, "extra"),
            variable_type_node(&fixture, "readonlyMissing"),
            variable_type_node(&fixture, "readonlyExtra"),
        ];
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for node in nodes {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics),
                Ok(error_type)
            );
        }
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| (
                    diagnostic.diagnostic.code(),
                    diagnostic.diagnostic.arguments.clone(),
                ))
                .collect::<Vec<_>>(),
            [
                (2314, vec!["Array<Element>".to_owned(), "1".to_owned()],),
                (2314, vec!["Array<Element>".to_owned(), "1".to_owned()],),
                (2314, vec!["ReadonlyArray<Item>".to_owned(), "1".to_owned()],),
                (2314, vec!["ReadonlyArray<Item>".to_owned(), "1".to_owned()],),
            ]
        );
        let warm = store_state(&fixture.store);
        for node in nodes {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics),
                Ok(error_type)
            );
        }
        assert_eq!(store_state(&fixture.store), warm);
        assert_eq!(
            diagnostics.len(),
            4,
            "warm queries must not repeat diagnostics"
        );
    }

    #[test]
    fn direct_global_array_local_aliases_do_not_enter_the_authoritative_fast_path() {
        let mut fixture = global_array_fixture(concat!(
            "function f() { ",
            "type Array<T> = T; type ReadonlyArray<T> = T; ",
            "let localMutable: Array<string>; ",
            "let localReadonly: ReadonlyArray<number>; ",
            "}",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let local_mutable = variable_type_node(&fixture, "localMutable");
        let local_readonly = variable_type_node(&fixture, "localReadonly");
        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert_eq!(
            query_global_node(&mut fixture, &global_types, local_mutable, &mut diagnostics,),
            Ok(string)
        );
        assert_eq!(
            query_global_node(
                &mut fixture,
                &global_types,
                local_readonly,
                &mut diagnostics,
            ),
            Ok(number)
        );
        for node in [local_mutable, local_readonly] {
            let symbol = fixture
                .store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol)
                .unwrap();
            assert_ne!(
                symbol,
                fixture
                    .store
                    .type_payload(global_types.array_type)
                    .unwrap()
                    .symbol()
                    .unwrap()
            );
            assert_ne!(
                symbol,
                fixture
                    .store
                    .type_payload(global_types.readonly_array_type)
                    .unwrap()
                    .symbol()
                    .unwrap()
            );
        }
        let warm = store_state(&fixture.store);
        assert_eq!(
            query_node(&mut fixture, local_mutable, &mut diagnostics),
            Ok(string)
        );
        assert_eq!(
            query_node(&mut fixture, local_readonly, &mut diagnostics),
            Ok(number)
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_global_array_warmed_nodes_aliases_and_unions_fail_closed_without_globals() {
        let mut fixture = global_array_fixture(concat!(
            "let direct: Array<number>; ",
            "let union: Array<number> | null; ",
            "type DirectAlias = Array<number>; ",
            "type UnionAlias = Array<number> | null; ",
            "type NestedUnionAlias = DirectAlias | null;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let direct = variable_type_node(&fixture, "direct");
        let union = variable_type_node(&fixture, "union");
        let direct_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "DirectAlias");
        let union_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "UnionAlias");
        let nested_union_alias = named_symbol(
            &fixture,
            SyntaxKind::TypeAliasDeclaration,
            "NestedUnionAlias",
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let direct_type =
            query_global_node(&mut fixture, &global_types, direct, &mut diagnostics).unwrap();
        assert!(query_global_node(&mut fixture, &global_types, union, &mut diagnostics).is_ok());
        assert!(
            query_global_declared(&mut fixture, &global_types, direct_alias, &mut diagnostics,)
                .is_ok()
        );
        assert!(
            query_global_declared(
                &mut fixture,
                &global_types,
                nested_union_alias,
                &mut diagnostics,
            )
            .is_ok()
        );
        assert!(
            query_global_declared(&mut fixture, &global_types, union_alias, &mut diagnostics,)
                .is_ok()
        );
        let warm = store_state(&fixture.store);

        assert!(matches!(
            query_node(&mut fixture, direct, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
            )) if error_node == direct
        ));
        assert_eq!(
            query_node(&mut fixture, union, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(direct_type)
            ))
        );
        assert!(matches!(
            query_declared(
                &mut fixture,
                direct_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(_)
            ))
        ));
        assert_eq!(
            query_declared(
                &mut fixture,
                union_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(direct_type)
            ))
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                nested_union_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(direct_type)
            ))
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_array_alias_roots_require_capability_even_with_an_empty_host() {
        let mut fixture = global_array_fixture(concat!(
            "type Direct = Array<number>; ",
            "type Shorthand = number[]; ",
            "type Through = Direct; ",
            "type Reduced = Through | null;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let aliases = ["Direct", "Shorthand", "Through", "Reduced"]
            .map(|name| named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, name));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let array_type =
            query_global_declared(&mut fixture, &global_types, aliases[0], &mut diagnostics)
                .unwrap();
        for alias in aliases.iter().skip(1) {
            assert_eq!(
                query_global_declared(&mut fixture, &global_types, *alias, &mut diagnostics,),
                Ok(array_type),
                "loose null reduction and transitive aliases retain the array root",
            );
        }
        let warm = store_state(&fixture.store);

        for alias in aliases {
            assert_eq!(
                query_empty_host_declared(&mut fixture, alias, &mut diagnostics),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedUnionConstituentType(array_type),
                )),
            );
            assert_eq!(store_state(&fixture.store), warm);
            assert_eq!(
                query_empty_host_global_declared(
                    &mut fixture,
                    &global_types,
                    alias,
                    &mut diagnostics,
                ),
                Ok(array_type),
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_generic_wrappers_replan_only_when_their_result_contains_an_array() {
        let mut fixture = global_array_fixture(concat!(
            "type Box<T> = T; ",
            "let direct: Box<Array<number>>; ",
            "let readonly: Box<ReadonlyArray<number>>; ",
            "let shorthand: Box<number[]>; ",
            "let plain: Box<number>;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let direct = variable_type_node(&fixture, "direct");
        let readonly = variable_type_node(&fixture, "readonly");
        let shorthand = variable_type_node(&fixture, "shorthand");
        let plain = variable_type_node(&fixture, "plain");
        let direct_array = type_reference_argument_node(&fixture, direct, 0);
        let readonly_array = type_reference_argument_node(&fixture, readonly, 0);
        let shorthand_array = type_reference_argument_node(&fixture, shorthand, 0);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let direct_type =
            query_global_node(&mut fixture, &global_types, direct, &mut diagnostics).unwrap();
        let readonly_type =
            query_global_node(&mut fixture, &global_types, readonly, &mut diagnostics).unwrap();
        let shorthand_type =
            query_global_node(&mut fixture, &global_types, shorthand, &mut diagnostics).unwrap();
        let plain_type =
            query_global_node(&mut fixture, &global_types, plain, &mut diagnostics).unwrap();
        let warm = store_state(&fixture.store);

        assert!(matches!(
            query_node(&mut fixture, direct, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
            )) if error_node == direct_array
        ));
        assert_eq!(store_state(&fixture.store), warm);
        assert!(matches!(
            query_node(&mut fixture, readonly, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
            )) if error_node == readonly_array
        ));
        assert_eq!(store_state(&fixture.store), warm);
        assert_eq!(
            query_node(&mut fixture, shorthand, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: shorthand_array,
                    kind: SyntaxKind::ArrayType,
                },
            )),
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert_eq!(
            query_node(&mut fixture, plain, &mut diagnostics),
            Ok(plain_type),
            "an unrelated fully cached generic alias keeps the empty capability fast path",
        );
        assert_eq!(store_state(&fixture.store), warm);

        for (node, expected) in [
            (direct, direct_type),
            (readonly, readonly_type),
            (shorthand, shorthand_type),
        ] {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics,),
                Ok(expected),
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_erased_generic_arguments_still_close_over_array_syntax() {
        let mut fixture = global_array_fixture(concat!(
            "type Ignore<T> = number; ",
            "let direct: Ignore<Array<number>>; ",
            "let readonly: Ignore<ReadonlyArray<number>>; ",
            "let shorthand: Ignore<number[]>; ",
            "let plain: Ignore<string>;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let direct = variable_type_node(&fixture, "direct");
        let readonly = variable_type_node(&fixture, "readonly");
        let shorthand = variable_type_node(&fixture, "shorthand");
        let plain = variable_type_node(&fixture, "plain");
        let direct_array = type_reference_argument_node(&fixture, direct, 0);
        let readonly_array = type_reference_argument_node(&fixture, readonly, 0);
        let shorthand_array = type_reference_argument_node(&fixture, shorthand, 0);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for node in [direct, readonly, shorthand, plain] {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics,),
                Ok(number),
            );
        }
        let warm = store_state(&fixture.store);

        for (node, array) in [(direct, direct_array), (readonly, readonly_array)] {
            assert!(matches!(
                query_node(&mut fixture, node, &mut diagnostics),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
                )) if error_node == array
            ));
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert_eq!(
            query_node(&mut fixture, shorthand, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: shorthand_array,
                    kind: SyntaxKind::ArrayType,
                },
            )),
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert_eq!(
            query_node(&mut fixture, plain, &mut diagnostics),
            Ok(number),
        );
        assert_eq!(store_state(&fixture.store), warm);

        for node in [direct, readonly, shorthand] {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics,),
                Ok(number),
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn cached_erased_type_literal_arguments_close_over_property_array_syntax() {
        let mut fixture = global_array_fixture(concat!(
            "type Ignore<T> = number; ",
            "let direct: Ignore<{ values: Array<number> }>; ",
            "let readonly: Ignore<{ values: ReadonlyArray<number> }>; ",
            "let shorthand: Ignore<{ values: number[] }>;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let direct = variable_type_node(&fixture, "direct");
        let readonly = variable_type_node(&fixture, "readonly");
        let shorthand = variable_type_node(&fixture, "shorthand");
        let direct_array = property_type_literal_child(
            &fixture,
            type_reference_argument_node(&fixture, direct, 0),
            0,
        );
        let readonly_array = property_type_literal_child(
            &fixture,
            type_reference_argument_node(&fixture, readonly, 0),
            0,
        );
        let shorthand_array = property_type_literal_child(
            &fixture,
            type_reference_argument_node(&fixture, shorthand, 0),
            0,
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        for node in [direct, readonly, shorthand] {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics,),
                Ok(number),
            );
        }
        let warm = store_state(&fixture.store);

        for (node, array) in [(direct, direct_array), (readonly, readonly_array)] {
            assert!(matches!(
                query_node(&mut fixture, node, &mut diagnostics),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
                )) if error_node == array
            ));
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert_eq!(
            query_node(&mut fixture, shorthand, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: shorthand_array,
                    kind: SyntaxKind::ArrayType,
                },
            )),
        );
        assert_eq!(store_state(&fixture.store), warm);

        for node in [direct, readonly, shorthand] {
            assert_eq!(
                query_global_node(&mut fixture, &global_types, node, &mut diagnostics,),
                Ok(number),
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn declared_property_array_closures_are_cycle_safe_and_reject_cache_poison() {
        let mut fixture = global_array_fixture(concat!(
            "interface Holder { values: Array<number>; } ",
            "interface Node { next: Node; children: Array<Node>; } ",
            "type MaybeHolder = Holder; ",
            "type MaybeNode = Node; ",
            "type Item = { values: Array<number> }; ",
            "type ThroughItem = Item;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let holder_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "MaybeHolder");
        let node_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "MaybeNode");
        let through_item_alias =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ThroughItem");
        let item_array_node =
            property_type_literal_child(&fixture, alias_parts(&fixture, "Item").2, 0);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let holder_type =
            query_global_declared(&mut fixture, &global_types, holder_alias, &mut diagnostics)
                .unwrap();
        let node_type =
            query_global_declared(&mut fixture, &global_types, node_alias, &mut diagnostics)
                .unwrap();
        let item_type = query_global_declared(
            &mut fixture,
            &global_types,
            through_item_alias,
            &mut diagnostics,
        )
        .unwrap();
        let holder_properties =
            object_members::resolved_declared_property_types(&fixture.store, holder_type).unwrap();
        let node_properties =
            object_members::resolved_declared_property_types(&fixture.store, node_type).unwrap();
        let holder_array = holder_properties[0];
        let node_array = node_properties[1];
        let item_array =
            object_members::resolved_declared_property_types(&fixture.store, item_type).unwrap()[0];
        let (number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };

        let node_or_array = fixture
            .store
            .expression_union_type_with_global_types(
                &global_types,
                &[node_type, node_array],
                UnionReduction::None,
            )
            .unwrap();
        assert_eq!(
            fixture.store.expression_union_type_with_global_types(
                &global_types,
                &[node_array, node_type],
                UnionReduction::None,
            ),
            Ok(node_or_array),
        );
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        for _ in 0..2 {
            assert_eq!(
                fixture
                    .store
                    .validate_cached_union_result_with_array_targets(targets, node_or_array, None,),
                Ok(()),
                "declared-object graph visits must not poison the strict union stack",
            );
        }
        let warm = store_state(&fixture.store);

        assert!(matches!(
            query_declared(
                &mut fixture,
                through_item_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
            )) if error_node == item_array_node
        ));
        assert_eq!(store_state(&fixture.store), warm);

        for (alias, hidden_array) in [
            (holder_alias, holder_array),
            (node_alias, node_array),
            (through_item_alias, item_array),
        ] {
            assert_eq!(
                query_empty_host_declared(&mut fixture, alias, &mut diagnostics),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedUnionConstituentType(hidden_array),
                )),
            );
            assert_eq!(store_state(&fixture.store), warm);
            assert!(
                query_empty_host_global_declared(
                    &mut fixture,
                    &global_types,
                    alias,
                    &mut diagnostics,
                )
                .is_ok()
            );
            assert_eq!(store_state(&fixture.store), warm);
        }

        assert!(fixture.store.set_type_reference_resolution(
            holder_array,
            None,
            Some(vec![string]),
        ));
        let poisoned = store_state(&fixture.store);
        for with_globals in [false, true] {
            let result = if with_globals {
                query_empty_host_global_declared(
                    &mut fixture,
                    &global_types,
                    holder_alias,
                    &mut diagnostics,
                )
            } else {
                query_empty_host_declared(&mut fixture, holder_alias, &mut diagnostics)
            };
            assert_eq!(
                result,
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedArrayType(holder_array),
                )),
            );
            assert_eq!(store_state(&fixture.store), poisoned);
        }
        assert!(fixture.store.set_type_reference_resolution(
            holder_array,
            None,
            Some(vec![number]),
        ));
        assert_eq!(
            query_empty_host_global_declared(
                &mut fixture,
                &global_types,
                holder_alias,
                &mut diagnostics,
            ),
            Ok(holder_type),
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn declared_type_literal_alias_provenance_is_symmetric_and_repairable() {
        let mut fixture = global_array_fixture(concat!(
            "type Item = { value: number }; ",
            "type Through = Item; ",
            "type Reduced = Through;",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let item_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Item");
        let reduced_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Reduced");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let item =
            query_global_declared(&mut fixture, &global_types, reduced_alias, &mut diagnostics)
                .unwrap();
        let alias = fixture
            .store
            .type_payload(item)
            .and_then(TypeRecord::alias)
            .expect("a direct alias-owned type literal retains its alias record");
        assert!(
            fixture
                .store
                .type_alias_declared_type_owners(item)
                .is_some_and(|owners| owners.contains(&item_alias))
        );
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Valid(
                object_members::DeclaredPropertyObjectProof::TypeLiteral,
            ),
        );

        assert!(fixture.store.set_type_alias(item, None));
        let poisoned = store_state(&fixture.store);
        for with_globals in [false, true] {
            let result = if with_globals {
                query_empty_host_global_declared(
                    &mut fixture,
                    &global_types,
                    reduced_alias,
                    &mut diagnostics,
                )
            } else {
                query_empty_host_declared(&mut fixture, reduced_alias, &mut diagnostics)
            };
            assert_eq!(
                result,
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedUnionType(item),
                )),
            );
            assert_eq!(store_state(&fixture.store), poisoned);
        }
        assert!(fixture.store.set_type_alias(item, Some(alias)));
        assert_eq!(
            query_empty_host_global_declared(
                &mut fixture,
                &global_types,
                reduced_alias,
                &mut diagnostics,
            ),
            Ok(item),
        );
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Valid(
                object_members::DeclaredPropertyObjectProof::TypeLiteral,
            ),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn exported_property_alias_provenance_is_a_valid_cached_boundary() {
        let mut fixture = fixture_with_module_state(
            "export type Item = { value: number };",
            CanonicalModuleState::External,
        );
        let item_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Item");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let item = query_declared(
            &mut fixture,
            item_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::NotDeclared,
        );
        let warm = store_state(&fixture.store);
        assert_eq!(
            query_empty_host_declared(&mut fixture, item_alias, &mut diagnostics),
            Ok(item),
            "a fully cached exported alias stays opaque outside the property-only proof",
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn exported_property_alias_boundaries_still_scan_hidden_array_types() {
        let mut fixture = global_array_fixture("export type Item = { values: Array<number> };");
        let global_types = initialize_fixture_global_types(&mut fixture);
        let item_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Item");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let item = query_global_declared(&mut fixture, &global_types, item_alias, &mut diagnostics)
            .unwrap();
        let hidden_array =
            object_members::resolved_declared_property_types(&fixture.store, item).unwrap()[0];
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::NotDeclared,
        );
        let boundary = store_state(&fixture.store);
        assert_eq!(
            query_empty_host_declared(&mut fixture, item_alias, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(hidden_array),
            )),
        );
        assert_eq!(store_state(&fixture.store), boundary);
        assert_eq!(
            query_empty_host_global_declared(
                &mut fixture,
                &global_types,
                item_alias,
                &mut diagnostics,
            ),
            Ok(item),
        );
        assert_eq!(store_state(&fixture.store), boundary);
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::NotDeclared,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn nested_property_alias_boundaries_close_over_hidden_array_capabilities() {
        let mut fixture = global_array_fixture(concat!(
            "namespace Outer { ",
            "type Item = { values: Array<number> }; ",
            "type Through = Item; ",
            "}",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let through = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Through");
        let item_literal = alias_parts(&fixture, "Item").2;
        let array_node = property_type_literal_child(&fixture, item_literal, 0);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let cold = store_state(&fixture.store);

        assert!(matches!(
            query_declared(
                &mut fixture,
                through,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(error_node)
            )) if error_node == array_node
        ));
        assert_eq!(store_state(&fixture.store), cold);

        let item =
            query_global_declared(&mut fixture, &global_types, through, &mut diagnostics).unwrap();
        let hidden_array =
            object_members::resolved_declared_property_types(&fixture.store, item).unwrap()[0];
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::NotDeclared,
        );
        let warm = store_state(&fixture.store);

        assert_eq!(
            query_empty_host_declared(&mut fixture, through, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(hidden_array),
            )),
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert_eq!(
            query_empty_host_global_declared(
                &mut fixture,
                &global_types,
                through,
                &mut diagnostics,
            ),
            Ok(item),
        );
        assert_eq!(store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn declared_owner_relationship_and_back_edge_poisons_are_repairable() {
        let mut fixture = global_array_fixture("interface Item { value: number; }");
        let global_types = initialize_fixture_global_types(&mut fixture);
        let item_symbol = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Item");
        let array_symbol = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Array");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let item =
            query_global_declared(&mut fixture, &global_types, item_symbol, &mut diagnostics)
                .unwrap();
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Valid(
                object_members::DeclaredPropertyObjectProof::Interface,
            ),
        );

        let (members, exports, parent, export_symbol) = {
            let owner = fixture.store.symbol(item_symbol).unwrap();
            (
                owner.members(),
                owner.exports(),
                owner.parent(),
                owner.export_symbol(),
            )
        };
        assert!(fixture.store.set_symbol_relationships(
            item_symbol,
            members,
            exports,
            Some(array_symbol),
            export_symbol,
        ));
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Malformed,
            "a top-level declaration cannot acquire a nested owner relationship",
        );
        assert!(fixture.store.set_symbol_relationships(
            item_symbol,
            members,
            exports,
            parent,
            export_symbol,
        ));
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Valid(
                object_members::DeclaredPropertyObjectProof::Interface,
            ),
        );

        let original_links = fixture
            .store
            .declared_type_links(item_symbol)
            .cloned()
            .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let mut poisoned_links = original_links.clone();
        poisoned_links.declared_type = Some(number);
        assert!(
            fixture
                .store
                .set_declared_type_links(item_symbol, poisoned_links)
        );
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Malformed,
            "a contradictory declared-type back edge is cache corruption",
        );
        assert!(
            fixture
                .store
                .set_declared_type_links(item_symbol, original_links)
        );
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Valid(
                object_members::DeclaredPropertyObjectProof::Interface,
            ),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn bound_merged_property_declarations_are_an_unsupported_declared_object_boundary() {
        let mut fixture = global_array_fixture(concat!(
            "interface Item { values: Array<number>; } ",
            "interface Item { values: Array<number>; }",
        ));
        let global_types = initialize_fixture_global_types(&mut fixture);
        let item_symbol = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Item");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members = fixture
            .store
            .symbol(item_symbol)
            .unwrap()
            .members()
            .unwrap();
        let item_property = fixture
            .store
            .symbol_table(members)
            .unwrap()
            .get_source("values")
            .unwrap();
        let declarations = fixture
            .store
            .symbol(item_property)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        assert_eq!(declarations.len(), 2);
        assert_ne!(declarations[0], declarations[1]);
        assert!(declarations.iter().all(|declaration| {
            fixture.store.source_node_kind(*declaration) == Some(SyntaxKind::PropertyDeclaration)
        }));
        let cold = store_state(&fixture.store);

        assert!(matches!(
            query_global_declared(&mut fixture, &global_types, item_symbol, &mut diagnostics,),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::InvalidInterfaceDeclaration(_)
            ))
        ));
        assert_eq!(store_state(&fixture.store), cold);

        let flags = fixture.store.symbol(item_symbol).unwrap().flags();
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let item = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            item_symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::NotDeclared,
            "real interface augmentation is outside the single-owner property domain",
        );
        assert!(matches!(
            object_members::validate_resolved_declared_property_type_graph(&fixture.store, item),
            object_members::DeclaredPropertyTypeGraphValidation::Opaque,
        ));

        assert!(fixture.store.set_symbol_declarations(
            item_property,
            Some(vec![declarations[0], declarations[0]]),
            Some(declarations[0]),
        ));
        assert_eq!(
            object_members::validate_resolved_declared_property_object(&fixture.store, item),
            object_members::DeclaredPropertyObjectValidation::Malformed,
            "repeated declaration identities remain cache corruption",
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_global_array_cache_poison_fails_atomically_and_retries() {
        let mut fixture = global_array_fixture("let literal: Array<'x'>; let warm: Array<number>;");
        let global_types = initialize_fixture_global_types(&mut fixture);
        let literal = variable_type_node(&fixture, "literal");
        let literal_argument = type_reference_argument_node(&fixture, literal, 0);
        let warm = variable_type_node(&fixture, "warm");
        let (any, number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.number_type,
                bootstrap.string_type,
            )
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert!(fixture.store.set_type_reference_resolution(
            global_types.any_array_type,
            None,
            Some(vec![number]),
        ));
        let poisoned_target = store_state(&fixture.store);
        assert!(matches!(
            query_global_node(&mut fixture, &global_types, literal, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == literal
        ));
        assert_eq!(store_state(&fixture.store), poisoned_target);
        assert!(fixture.store.type_node_links(literal).is_none());
        assert!(fixture.store.type_node_links(literal_argument).is_none());
        assert!(fixture.store.set_type_reference_resolution(
            global_types.any_array_type,
            None,
            Some(vec![any]),
        ));

        let literal_type =
            query_global_node(&mut fixture, &global_types, literal, &mut diagnostics).unwrap();
        let literal_argument_type = fixture
            .store
            .type_node_links(literal_argument)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let warm_type =
            query_global_node(&mut fixture, &global_types, warm, &mut diagnostics).unwrap();
        let readonly_number = fixture
            .store
            .create_canonical_array_type(&global_types, number, true)
            .unwrap();
        assert!(fixture.store.set_type_node_links(
            warm,
            TypeNodeLinks {
                resolved_type: Some(readonly_number),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned_node = store_state(&fixture.store);
        assert!(matches!(
            query_global_node(&mut fixture, &global_types, warm, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == warm
        ));
        assert_eq!(store_state(&fixture.store), poisoned_node);
        assert!(fixture.store.set_type_node_links(
            warm,
            TypeNodeLinks {
                resolved_type: Some(warm_type),
                ..TypeNodeLinks::default()
            },
        ));
        let array_symbol = fixture
            .store
            .type_payload(global_types.array_type)
            .unwrap()
            .symbol()
            .unwrap();
        let readonly_symbol = fixture
            .store
            .type_payload(global_types.readonly_array_type)
            .unwrap()
            .symbol()
            .unwrap();
        assert!(fixture.store.set_symbol_node_links(
            warm,
            SymbolNodeLinks {
                resolved_symbol: Some(readonly_symbol),
            },
        ));
        let poisoned_symbol = store_state(&fixture.store);
        assert!(matches!(
            query_global_node(&mut fixture, &global_types, warm, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedSymbol {
                    node: error_node,
                    symbol,
                }
            )) if error_node == warm && symbol == readonly_symbol
        ));
        assert_eq!(store_state(&fixture.store), poisoned_symbol);
        assert!(fixture.store.set_symbol_node_links(
            warm,
            SymbolNodeLinks {
                resolved_symbol: Some(array_symbol),
            },
        ));

        assert!(fixture.store.set_type_node_links(
            literal_argument,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        let dirty_argument = store_state(&fixture.store);
        assert!(matches!(
            query_global_node(&mut fixture, &global_types, literal, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidTypeReference(error_node)
            )) if error_node == literal
        ));
        assert_eq!(store_state(&fixture.store), dirty_argument);
        assert!(fixture.store.set_type_node_links(
            literal_argument,
            TypeNodeLinks {
                resolved_type: Some(literal_argument_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            query_global_node(&mut fixture, &global_types, literal, &mut diagnostics),
            Ok(literal_type)
        );
        assert_eq!(
            query_global_node(&mut fixture, &global_types, warm, &mut diagnostics),
            Ok(warm_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn function_type_cold_warm_signature_parameters_and_optionality_are_exact() {
        let mut fixture = fixture_with_intrinsic(
            "type Fn = (required: 1, optional?: (2),) => 3;",
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Fn");
        let function = function_type_node(&fixture, "Fn");
        let parameters = function_parameter_nodes(&fixture, function);
        let parameter_symbols = parameters
            .iter()
            .map(|parameter| node_symbol(&fixture, *parameter))
            .collect::<Vec<_>>();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = query_node(&mut fixture, function, &mut diagnostics).unwrap();
        assert_eq!(
            fixture.store.type_alias_links(alias),
            Some(&TypeAliasLinks {
                declared_type: Some(type_),
                ..TypeAliasLinks::default()
            })
        );
        let signature_id = function_signature(&fixture.store, function);
        let signature = fixture.store.signature(signature_id).unwrap();
        assert_eq!(signature.flags(), SignatureFlags::HAS_LITERAL_TYPES);
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(signature.resolved_min_argument_count(), -1);
        assert_eq!(signature.declaration(), Some(function));
        assert!(signature.type_parameters().is_empty());
        assert_eq!(signature.parameters(), parameter_symbols);
        assert!(signature.this_parameter().is_none());
        assert!(signature.resolved_return_type().is_none());
        assert!(signature.resolved_type_predicate().is_none());
        assert!(signature.target().is_none());
        assert!(signature.mapper().is_none());
        assert!(signature.isolated_signature_type().is_none());
        assert!(signature.composite().is_none());

        let record = fixture.store.type_payload(type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(record.symbol(), Some(node_symbol(&fixture, function)));
        assert_eq!(
            record
                .alias()
                .and_then(|alias| fixture.store.type_alias(alias))
                .and_then(TypeAlias::symbol),
            Some(alias)
        );
        let structured = record.data().structured().unwrap();
        assert_eq!(
            structured.members,
            fixture
                .store
                .symbol(node_symbol(&fixture, function))
                .unwrap()
                .members()
        );
        assert_eq!(structured.properties.as_deref(), Some(&[][..]));
        assert_eq!(structured.signatures.as_deref(), Some(&[signature_id][..]));
        assert_eq!(structured.call_signature_count, 1);
        assert!(structured.index_infos.is_none());

        let required = fixture
            .store
            .value_symbol_links(parameter_symbols[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture.store.type_payload(required).unwrap().flags(),
            TypeFlags::NUMBER_LITERAL
        );
        let optional = fixture
            .store
            .value_symbol_links(parameter_symbols[1])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let undefined = fixture.store.intrinsic_bootstrap().unwrap().undefined_type;
        assert!(union_types(&fixture.store, optional).contains(&undefined));
        assert!(union_types(&fixture.store, optional).iter().any(|type_| {
            fixture
                .store
                .type_payload(*type_)
                .is_some_and(|record| record.flags() == TypeFlags::NUMBER_LITERAL)
        }));
        let return_node = function_return_node(&fixture, function);
        assert!(fixture.store.type_node_links(return_node).is_none());

        let warm = function_store_state(&fixture.store);
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(type_)
        );
        assert_eq!(function_store_state(&fixture.store), warm);

        let return_type =
            query_signature_return(&mut fixture, signature_id, &mut diagnostics).unwrap();
        assert_eq!(
            fixture.store.type_payload(return_type).unwrap().flags(),
            TypeFlags::NUMBER_LITERAL
        );
        let return_warm = function_store_state(&fixture.store);
        assert_eq!(
            query_signature_return(&mut fixture, signature_id, &mut diagnostics),
            Ok(return_type)
        );
        assert_eq!(function_store_state(&fixture.store), return_warm);
        assert!(diagnostics.is_empty());

        let mut loose = self::fixture("type Loose = (value?: void) => void;");
        let loose_alias = named_symbol(&loose, SyntaxKind::TypeAliasDeclaration, "Loose");
        let loose_function = function_type_node(&loose, "Loose");
        let loose_parameter = function_parameter_nodes(&loose, loose_function)[0];
        let loose_parameter_symbol = node_symbol(&loose, loose_parameter);
        let loose_type = query_declared(
            &mut loose,
            loose_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let loose_signature = loose
            .store
            .signature(function_signature(&loose.store, loose_function))
            .unwrap();
        assert_eq!(loose_signature.flags(), SignatureFlags::NONE);
        assert_eq!(loose_signature.min_argument_count(), 0);
        assert_eq!(
            loose
                .store
                .value_symbol_links(loose_parameter_symbol)
                .and_then(|links| links.resolved_type),
            Some(loose.store.intrinsic_bootstrap().unwrap().void_type)
        );
        let loose_warm = function_store_state(&loose.store);
        assert_eq!(
            query_declared(
                &mut loose,
                loose_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(loose_type)
        );
        assert_eq!(function_store_state(&loose.store), loose_warm);

        let mut parenthesized = self::fixture("type Parenthesized = (value: (1)) => void;");
        let parenthesized_alias = named_symbol(
            &parenthesized,
            SyntaxKind::TypeAliasDeclaration,
            "Parenthesized",
        );
        let parenthesized_function = function_type_node(&parenthesized, "Parenthesized");
        query_declared(
            &mut parenthesized,
            parenthesized_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(
            parenthesized
                .store
                .signature(function_signature(
                    &parenthesized.store,
                    parenthesized_function,
                ))
                .unwrap()
                .flags(),
            SignatureFlags::NONE
        );

        let mut named = fixture_with_intrinsic(
            "type Maybe = number | undefined; type Named = (value?: Maybe) => void;",
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );
        let maybe = named_symbol(&named, SyntaxKind::TypeAliasDeclaration, "Maybe");
        let named_alias = named_symbol(&named, SyntaxKind::TypeAliasDeclaration, "Named");
        let named_function = function_type_node(&named, "Named");
        let named_parameter = function_parameter_nodes(&named, named_function)[0];
        let named_parameter_symbol = node_symbol(&named, named_parameter);
        let maybe_type = query_declared(
            &mut named,
            maybe,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let named_union_state = (
            named.store.intrinsic_bootstrap().unwrap().union_cache_len(),
            named
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
        );
        let named_type = query_declared(
            &mut named,
            named_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert_eq!(
            (
                named.store.intrinsic_bootstrap().unwrap().union_cache_len(),
                named
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_of_union_cache_len(),
            ),
            named_union_state
        );
        assert_eq!(
            named
                .store
                .value_symbol_links(named_parameter_symbol)
                .and_then(|links| links.resolved_type),
            Some(maybe_type)
        );
        let named_warm = function_store_state(&named.store);
        assert_eq!(
            query_declared(
                &mut named,
                named_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(named_type)
        );
        assert_eq!(function_store_state(&named.store), named_warm);

        let mut edges = fixture_with_intrinsic(
            concat!(
                "type Pair = string | number; ",
                "type Edges = (voidValue?: void, nullValue?: null, pair?: Pair) => void;",
            ),
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );
        let pair = named_symbol(&edges, SyntaxKind::TypeAliasDeclaration, "Pair");
        let edges_alias = named_symbol(&edges, SyntaxKind::TypeAliasDeclaration, "Edges");
        let edges_function = function_type_node(&edges, "Edges");
        let edge_parameters = function_parameter_nodes(&edges, edges_function);
        let edges_type = query_declared(
            &mut edges,
            edges_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let pair_type = edges
            .store
            .type_alias_links(pair)
            .and_then(|links| links.declared_type)
            .unwrap();
        let (void_type, null_type, undefined_type) = {
            let bootstrap = edges.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.void_type,
                bootstrap.null_type,
                bootstrap.undefined_type,
            )
        };
        for (index, base) in [(0, void_type), (1, null_type)] {
            let parameter_type = edges
                .store
                .value_symbol_links(node_symbol(&edges, edge_parameters[index]))
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert!(union_types(&edges.store, parameter_type).contains(&base));
            assert!(union_types(&edges.store, parameter_type).contains(&undefined_type));
        }
        let optional_pair = edges
            .store
            .value_symbol_links(node_symbol(&edges, edge_parameters[2]))
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_ne!(optional_pair, pair_type);
        assert!(union_types(&edges.store, optional_pair).contains(&undefined_type));
        let edge_warm = function_store_state(&edges.store);
        assert_eq!(
            query_declared(
                &mut edges,
                edges_alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(edges_type)
        );
        assert_eq!(function_store_state(&edges.store), edge_warm);

        let mut arrays = global_array_fixture("type Fn = (value: Array<number>) => void;");
        let global_types = initialize_fixture_global_types(&mut arrays);
        let array_alias = named_symbol(&arrays, SyntaxKind::TypeAliasDeclaration, "Fn");
        let array_function = function_type_node(&arrays, "Fn");
        let array_parameter = function_parameter_nodes(&arrays, array_function)[0];
        let array_function_type =
            query_global_declared(&mut arrays, &global_types, array_alias, &mut diagnostics)
                .unwrap();
        let array_parameter_type = arrays
            .store
            .value_symbol_links(node_symbol(&arrays, array_parameter))
            .and_then(|links| links.resolved_type)
            .unwrap();
        let array_warm = function_store_state(&arrays.store);
        assert_eq!(
            query_empty_host_declared(&mut arrays, array_alias, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituentType(array_parameter_type)
            ))
        );
        assert_eq!(function_store_state(&arrays.store), array_warm);
        assert_eq!(
            query_empty_host_global_declared(
                &mut arrays,
                &global_types,
                array_alias,
                &mut diagnostics,
            ),
            Ok(array_function_type)
        );
        assert_eq!(function_store_state(&arrays.store), array_warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn function_type_recursive_alias_shells_cover_direct_and_mutual_optional_unions() {
        let mut fixture = fixture_with_intrinsic(
            concat!(
                "type SelfRef = (next: SelfRef) => SelfRef; ",
                "type UnionSelf = (next: UnionSelf | undefined) => void; ",
                "type Left = (right: Right | undefined) => Right; ",
                "type Right = (left: Left | undefined) => Left; ",
                "type Outer = ((next: Outer) => void) | undefined; ",
                "type OuterLeft = ((right: OuterRight) => void) | undefined; ",
                "type OuterRight = ((left: OuterLeft) => void) | undefined; ",
                "type Callback = { cb: (next: Callback) => void }; ",
                "type DirectObject = { next: DirectObject }; ",
                "type ThroughDirectObject = (value: ReachedDirectObject) => void; ",
                "type ReachedDirectObject = { next: ReachedDirectObject };",
            ),
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );
        let self_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "SelfRef");
        let union_self_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "UnionSelf");
        let left_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Left");
        let right_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Right");
        let outer_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Outer");
        let outer_left_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "OuterLeft");
        let outer_right_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "OuterRight");
        let callback_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Callback");
        let direct_object_symbol =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "DirectObject");
        let through_direct_object_symbol = named_symbol(
            &fixture,
            SyntaxKind::TypeAliasDeclaration,
            "ThroughDirectObject",
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let self_type = query_declared(
            &mut fixture,
            self_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let union_self_type = query_declared(
            &mut fixture,
            union_self_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let left_type = query_declared(
            &mut fixture,
            left_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let right_type = fixture
            .store
            .type_alias_links(right_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        assert_eq!(
            query_declared(
                &mut fixture,
                right_symbol,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(right_type)
        );
        let outer_type = query_declared(
            &mut fixture,
            outer_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let outer_left_type = query_declared(
            &mut fixture,
            outer_left_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let outer_right_type = fixture
            .store
            .type_alias_links(outer_right_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let callback_type = query_declared(
            &mut fixture,
            callback_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

        let resolved_parameter = |fixture: &Fixture, alias: &str| {
            let parameter =
                function_parameter_nodes(fixture, function_type_node(fixture, alias))[0];
            fixture
                .store
                .value_symbol_links(node_symbol(fixture, parameter))
                .and_then(|links| links.resolved_type)
                .unwrap()
        };
        assert_eq!(resolved_parameter(&fixture, "SelfRef"), self_type);
        let undefined = fixture.store.intrinsic_bootstrap().unwrap().undefined_type;
        let union_self_parameter = resolved_parameter(&fixture, "UnionSelf");
        assert!(union_types(&fixture.store, union_self_parameter).contains(&union_self_type));
        assert!(union_types(&fixture.store, union_self_parameter).contains(&undefined));
        let left_parameter = resolved_parameter(&fixture, "Left");
        assert!(union_types(&fixture.store, left_parameter).contains(&right_type));
        assert!(union_types(&fixture.store, left_parameter).contains(&undefined));
        let right_parameter = resolved_parameter(&fixture, "Right");
        assert!(union_types(&fixture.store, right_parameter).contains(&left_type));
        assert!(union_types(&fixture.store, right_parameter).contains(&undefined));
        let outer_function_type = fixture
            .store
            .type_node_links(function_type_node(&fixture, "Outer"))
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert!(union_types(&fixture.store, outer_type).contains(&outer_function_type));
        assert!(union_types(&fixture.store, outer_type).contains(&undefined));
        assert_eq!(resolved_parameter(&fixture, "Outer"), outer_type);
        assert_eq!(resolved_parameter(&fixture, "OuterLeft"), outer_right_type);
        assert_eq!(resolved_parameter(&fixture, "OuterRight"), outer_left_type);
        assert_eq!(resolved_parameter(&fixture, "Callback"), callback_type);

        let before_direct_object = function_store_state(&fixture.store);
        assert!(matches!(
            query_declared(
                &mut fixture,
                direct_object_symbol,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::GenericReferenceUnsupported { .. }
            ))
        ));
        assert_eq!(function_store_state(&fixture.store), before_direct_object);
        assert!(matches!(
            query_declared(
                &mut fixture,
                through_direct_object_symbol,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::GenericReferenceUnsupported { .. }
            ))
        ));
        assert_eq!(function_store_state(&fixture.store), before_direct_object);

        let self_signature =
            function_signature(&fixture.store, function_type_node(&fixture, "SelfRef"));
        let union_self_signature =
            function_signature(&fixture.store, function_type_node(&fixture, "UnionSelf"));
        let left_signature =
            function_signature(&fixture.store, function_type_node(&fixture, "Left"));
        let right_signature =
            function_signature(&fixture.store, function_type_node(&fixture, "Right"));
        assert_eq!(
            query_signature_return(&mut fixture, self_signature, &mut diagnostics),
            Ok(self_type)
        );
        assert_eq!(
            query_signature_return(&mut fixture, union_self_signature, &mut diagnostics),
            Ok(fixture.store.intrinsic_bootstrap().unwrap().void_type)
        );
        assert_eq!(
            query_signature_return(&mut fixture, left_signature, &mut diagnostics),
            Ok(right_type)
        );
        assert_eq!(
            query_signature_return(&mut fixture, right_signature, &mut diagnostics),
            Ok(left_type)
        );
        for (symbol, expected) in [
            (outer_symbol, outer_type),
            (outer_left_symbol, outer_left_type),
            (outer_right_symbol, outer_right_type),
            (callback_symbol, callback_type),
        ] {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    symbol,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Ok(expected)
            );
        }
        let warm = function_store_state(&fixture.store);
        for (symbol, expected) in [
            (outer_symbol, outer_type),
            (outer_left_symbol, outer_left_type),
            (outer_right_symbol, outer_right_type),
            (callback_symbol, callback_type),
        ] {
            assert_eq!(
                query_declared(
                    &mut fixture,
                    symbol,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Ok(expected)
            );
        }
        assert_eq!(function_store_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn function_type_lazy_return_cycles_cache_any_once_and_balance_resolution() {
        let mut fixture = fixture("type Loop = Loop; type Fn = () => Loop;");
        let function_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Fn");
        let loop_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Loop");
        let function = function_type_node(&fixture, "Fn");
        let return_node = function_return_node(&fixture, function);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut fixture,
            function_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let signature = function_signature(&fixture.store, function);
        let (error_type, any_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.any_type)
        };

        assert!(
            fixture
                .store
                .push_type_resolution(
                    TypeResolutionTarget::Signature(signature),
                    TypeSystemPropertyName::ResolvedReturnType,
                )
                .unwrap()
        );
        assert_eq!(
            query_signature_return(&mut fixture, signature, &mut diagnostics),
            Ok(error_type)
        );
        assert!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type()
                .is_none()
        );
        assert_eq!(fixture.store.pop_type_resolution(), Some(false));
        assert!(diagnostics.is_empty());

        assert!(
            fixture
                .store
                .push_type_resolution(
                    TypeResolutionTarget::Symbol(loop_alias),
                    TypeSystemPropertyName::DeclaredType,
                )
                .unwrap()
        );
        assert_eq!(
            query_signature_return(&mut fixture, signature, &mut diagnostics),
            Ok(any_type)
        );
        assert_eq!(fixture.store.pop_type_resolution(), Some(false));
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2577);
        assert_eq!(diagnostics.as_slice()[0].node, Some(return_node));
        assert_eq!(
            fixture
                .store
                .type_node_links(return_node)
                .and_then(|links| links.resolved_type),
            Some(error_type)
        );
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(any_type)
        );
        assert!(fixture.store.signature_has_circular_return_type(signature));
        let warm = function_store_state(&fixture.store);
        assert_eq!(
            query_signature_return(&mut fixture, signature, &mut diagnostics),
            Ok(any_type)
        );
        assert_eq!(function_store_state(&fixture.store), warm);
        assert_eq!(diagnostics.len(), 1);
        let function_type = fixture
            .store
            .type_node_links(function)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            return_node,
            TypeNodeLinks {
                resolved_type: Some(string_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        let poisoned = function_store_state(&fixture.store);
        assert!(matches!(
            query_signature_return(&mut fixture, signature, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(type_)
            )) if type_ == function_type
        ));
        assert_eq!(function_store_state(&fixture.store), poisoned);
        assert!(fixture.store.set_type_node_links(
            return_node,
            TypeNodeLinks {
                resolved_type: Some(error_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );
        assert_eq!(
            query_signature_return(&mut fixture, signature, &mut diagnostics),
            Ok(any_type)
        );
        assert_eq!(diagnostics.len(), 1);
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(any_type))
        );
        assert!(!fixture.store.signature_has_circular_return_type(signature));
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));

        let mut cleared = self::fixture("type Loop = Loop; type Fn = () => Loop;");
        let cleared_alias = named_symbol(&cleared, SyntaxKind::TypeAliasDeclaration, "Fn");
        let cleared_loop = named_symbol(&cleared, SyntaxKind::TypeAliasDeclaration, "Loop");
        let cleared_function = function_type_node(&cleared, "Fn");
        let mut cleared_diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut cleared,
            cleared_alias,
            CanonicalTypeQueryOptions::default(),
            &mut cleared_diagnostics,
        )
        .unwrap();
        let cleared_signature = function_signature(&cleared.store, cleared_function);
        assert!(
            cleared
                .store
                .push_type_resolution(
                    TypeResolutionTarget::Symbol(cleared_loop),
                    TypeSystemPropertyName::DeclaredType,
                )
                .unwrap()
        );
        assert!(
            query_signature_return(&mut cleared, cleared_signature, &mut cleared_diagnostics,)
                .is_ok()
        );
        assert_eq!(cleared.store.pop_type_resolution(), Some(false));
        assert!(
            cleared
                .store
                .signature_has_circular_return_type(cleared_signature)
        );
        let foreign = self::fixture("type Foreign = string;")
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert!(
            !cleared
                .store
                .set_signature_resolved_return_type(cleared_signature, Some(foreign))
        );
        assert!(
            cleared
                .store
                .signature_has_circular_return_type(cleared_signature)
        );
        assert!(
            cleared
                .store
                .set_signature_resolved_return_type(cleared_signature, None)
        );
        assert!(
            !cleared
                .store
                .signature_has_circular_return_type(cleared_signature)
        );
        assert!(
            cleared
                .store
                .signature(cleared_signature)
                .unwrap()
                .resolved_return_type()
                .is_none()
        );
        let cleared_type = cleared
            .store
            .type_node_links(cleared_function)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            cleared.store.validate_union_constituent(cleared_type),
            Ok(())
        );

        let mut wrapped = global_array_fixture("type Loop = Loop; type Fn = () => Loop[];");
        let wrapped_globals = initialize_fixture_global_types(&mut wrapped);
        let wrapped_alias = named_symbol(&wrapped, SyntaxKind::TypeAliasDeclaration, "Fn");
        let wrapped_loop = named_symbol(&wrapped, SyntaxKind::TypeAliasDeclaration, "Loop");
        let wrapped_function = function_type_node(&wrapped, "Fn");
        let wrapped_return = function_return_node(&wrapped, wrapped_function);
        let mut wrapped_diagnostics = CanonicalCheckerDiagnostics::default();
        query_global_declared(
            &mut wrapped,
            &wrapped_globals,
            wrapped_alias,
            &mut wrapped_diagnostics,
        )
        .unwrap();
        let wrapped_signature = function_signature(&wrapped.store, wrapped_function);
        assert!(
            wrapped
                .store
                .push_type_resolution(
                    TypeResolutionTarget::Symbol(wrapped_loop),
                    TypeSystemPropertyName::DeclaredType,
                )
                .unwrap()
        );
        let wrapped_any = wrapped.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(
            query_global_signature_return(
                &mut wrapped,
                &wrapped_globals,
                wrapped_signature,
                &mut wrapped_diagnostics,
            ),
            Ok(wrapped_any)
        );
        assert_eq!(wrapped.store.pop_type_resolution(), Some(false));
        let wrapped_annotation = wrapped
            .store
            .type_node_links(wrapped_return)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            wrapped
                .store
                .circular_return_annotation_type(wrapped_signature),
            Some(wrapped_annotation)
        );
        assert_ne!(
            wrapped_annotation,
            wrapped.store.intrinsic_bootstrap().unwrap().error_type
        );
        assert_eq!(wrapped_diagnostics.len(), 1);
        assert_eq!(wrapped_diagnostics.as_slice()[0].diagnostic.code(), 2577);
        assert_eq!(
            query_global_signature_return(
                &mut wrapped,
                &wrapped_globals,
                wrapped_signature,
                &mut wrapped_diagnostics,
            ),
            Ok(wrapped_any)
        );
        assert_eq!(wrapped_diagnostics.len(), 1);

        let mut forged = self::fixture("type Loop = Loop; type Fn = () => Loop;");
        let function_alias = named_symbol(&forged, SyntaxKind::TypeAliasDeclaration, "Fn");
        let loop_alias = named_symbol(&forged, SyntaxKind::TypeAliasDeclaration, "Loop");
        let function = function_type_node(&forged, "Fn");
        let mut forged_diagnostics = CanonicalCheckerDiagnostics::default();
        query_declared(
            &mut forged,
            function_alias,
            CanonicalTypeQueryOptions::default(),
            &mut forged_diagnostics,
        )
        .unwrap();
        let forged_signature = function_signature(&forged.store, function);
        let error_type = forged.store.intrinsic_bootstrap().unwrap().error_type;
        let any_type = forged.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(
            query_declared(
                &mut forged,
                loop_alias,
                CanonicalTypeQueryOptions::default(),
                &mut forged_diagnostics,
            ),
            Ok(error_type)
        );
        assert!(
            forged
                .store
                .set_signature_resolved_return_type(forged_signature, Some(any_type))
        );
        assert!(
            !forged
                .store
                .signature_has_circular_return_type(forged_signature)
        );
        let forged_function_type = forged
            .store
            .type_node_links(function)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert!(matches!(
            forged.store.validate_union_constituent(forged_function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                if type_ == forged_function_type
        ));
        let forged_state = function_store_state(&forged.store);
        assert!(matches!(
            query_signature_return(
                &mut forged,
                forged_signature,
                &mut forged_diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(type_)
            )) if type_ == forged_function_type
        ));
        assert_eq!(function_store_state(&forged.store), forged_state);
        assert_eq!(forged_diagnostics.len(), 1);
        assert_eq!(forged_diagnostics.as_slice()[0].diagnostic.code(), 2456);
    }

    #[test]
    fn function_type_poison_is_read_only_and_exact_shells_retry_with_identity() {
        let mut signature_poison = fixture("type Fn = (value: string) => number;");
        let alias = named_symbol(&signature_poison, SyntaxKind::TypeAliasDeclaration, "Fn");
        let function = function_type_node(&signature_poison, "Fn");
        assert!(signature_poison.store.set_signature_links(
            function,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolving,
                ..SignatureLinks::default()
            },
        ));
        let poisoned = function_store_state(&signature_poison.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut signature_poison,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidFunctionType(node)
            )) if node == function
        ));
        assert_eq!(function_store_state(&signature_poison.store), poisoned);
        assert!(
            signature_poison
                .store
                .set_signature_links(function, SignatureLinks::default())
        );
        query_declared(
            &mut signature_poison,
            alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

        let mut fixture = fixture("type Fn = (value: { nested: string }) => number;");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Fn");
        let function = function_type_node(&fixture, "Fn");
        let parameter = function_parameter_nodes(&fixture, function)[0];
        let annotation = parameter_type_node(&fixture, parameter);
        let poison = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(matches!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidLiteralType(node)
            )) if node == annotation
        ));
        let shell = fixture
            .store
            .type_node_links(function)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let shell_signature = function_signature(&fixture.store, function);
        assert!(
            fixture
                .store
                .callable_signature_parameter_types(shell_signature)
                .is_none(),
            "pending parameter publication must not expose semantic provenance",
        );
        let structured = fixture
            .store
            .type_payload(shell)
            .unwrap()
            .data()
            .structured()
            .unwrap();
        assert_eq!(structured.call_signature_count, 1);
        assert_eq!(
            structured.signatures.as_deref(),
            Some(&[shell_signature][..])
        );
        assert!(
            fixture
                .store
                .value_symbol_links(node_symbol(&fixture, parameter))
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
        assert!(
            fixture
                .store
                .set_type_node_links(annotation, TypeNodeLinks::default())
        );
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(shell)
        );
        assert_eq!(
            function_signature(&fixture.store, function),
            shell_signature
        );
        let published_parameter_type = fixture
            .store
            .value_symbol_links(node_symbol(&fixture, parameter))
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(shell_signature),
            Some(std::slice::from_ref(&published_parameter_type)),
        );

        let parameter_symbol = node_symbol(&fixture, parameter);
        let correct_links = fixture
            .store
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .clone();
        assert!(fixture.store.set_value_symbol_links(
            parameter_symbol,
            ValueSymbolLinks {
                resolved_type: Some(poison),
                ..ValueSymbolLinks::default()
            },
        ));
        let warm_poison = function_store_state(&fixture.store);
        assert_eq!(
            functions::validate_stored_function_type(&fixture.store, shell),
            functions::StoredFunctionTypeValidation::Malformed,
        );
        let poisoned_result = query_node(&mut fixture, function, &mut diagnostics);
        assert!(matches!(
            poisoned_result,
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(type_)
            )) if type_ == shell
        ), "unexpected poisoned function result: {poisoned_result:?}");
        assert_eq!(function_store_state(&fixture.store), warm_poison);
        assert!(
            fixture
                .store
                .set_value_symbol_links(parameter_symbol, correct_links)
        );
        assert_eq!(
            query_node(&mut fixture, function, &mut diagnostics),
            Ok(shell)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn function_type_unsupported_phase_one_matrix_is_atomic() {
        let assert_unsupported = |mut fixture: Fixture| {
            let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Fn");
            let before = function_store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(matches!(
                query_declared(
                    &mut fixture,
                    alias,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax {
                        kind: SyntaxKind::FunctionType,
                        ..
                    }
                ))
            ));
            assert_eq!(function_store_state(&fixture.store), before);
            assert!(diagnostics.is_empty());
        };
        for source in [
            "type Fn<T> = (value: string) => number;",
            "type Fn = <T>(value: T) => T;",
            "type Fn = (this: object, value: string) => number;",
            "type Fn = (...value: string[]) => number;",
            "type Fn = ([value]: [string]) => number;",
            "type Fn = (value: string = \"\") => number;",
        ] {
            assert_unsupported(fixture(source));
        }
        assert_unsupported(fixture_with_mutation(
            "type Fn = (value: string) => number;",
            |parsed| {
                let parameter = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::Parameter).then_some(node)
                    })
                    .unwrap();
                let NodeData::ParameterDeclaration(data) =
                    &mut parsed.arena.get_mut(parameter).unwrap().data
                else {
                    unreachable!()
                };
                data.type_ = None;
            },
        ));
        assert_unsupported(fixture_with_mutation(
            "type Fn = (value: string) => number;",
            |parsed| {
                let function = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::FunctionType).then_some(node)
                    })
                    .unwrap();
                let NodeData::FunctionTypeNode(data) =
                    &mut parsed.arena.get_mut(function).unwrap().data
                else {
                    unreachable!()
                };
                data.type_ = None;
            },
        ));
        let mut lazy_boundary = fixture("type Fn = (value: string) => [string];");
        let alias = named_symbol(&lazy_boundary, SyntaxKind::TypeAliasDeclaration, "Fn");
        let function = function_type_node(&lazy_boundary, "Fn");
        let return_node = function_return_node(&lazy_boundary, function);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            query_declared(
                &mut lazy_boundary,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .is_ok()
        );
        let signature = function_signature(&lazy_boundary.store, function);
        let before_return = function_store_state(&lazy_boundary.store);
        assert_eq!(
            query_signature_return(&mut lazy_boundary, signature, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::UnsupportedSyntax {
                    node: return_node,
                    kind: SyntaxKind::TupleType,
                }
            ))
        );
        assert_eq!(function_store_state(&lazy_boundary.store), before_return);
        assert!(
            lazy_boundary
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type()
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn function_type_union_hook_rejects_barrier_and_signature_poison() {
        let mut fixture = fixture_with_intrinsic(
            "type Fn = (value?: string) => number; type Maybe = Fn | undefined;",
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );
        let function_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Fn");
        let maybe_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Maybe");
        let function = function_type_node(&fixture, "Fn");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = query_declared(
            &mut fixture,
            function_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let signature = function_signature(&fixture.store, function);
        let members = fixture
            .store
            .type_payload(function_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .unwrap();
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );

        assert!(fixture.store.set_structured_type_members(
            function_type,
            None,
            None,
            None,
            None,
            None,
        ));
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        assert!(fixture.store.set_structured_type_members(
            function_type,
            Some(members),
            Some(Vec::new()),
            Some(vec![signature]),
            None,
            None,
        ));
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );

        assert!(fixture.store.set_signature_links(
            function,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolving,
                ..SignatureLinks::default()
            },
        ));
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        assert!(fixture.store.set_signature_links(
            function,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );

        let parameter = function_parameter_nodes(&fixture, function)[0];
        let parameter_symbol = node_symbol(&fixture, parameter);
        let parameter_links = fixture
            .store
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .clone();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_value_symbol_links(
            parameter_symbol,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(matches!(
            functions::validate_stored_function_type(&fixture.store, function_type),
            functions::StoredFunctionTypeValidation::Malformed
        ));
        assert!(
            fixture
                .store
                .set_value_symbol_links(parameter_symbol, parameter_links.clone())
        );
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );
        assert!(
            fixture
                .store
                .set_value_symbol_links(parameter_symbol, ValueSymbolLinks::default())
        );
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        assert!(
            fixture
                .store
                .set_value_symbol_links(parameter_symbol, parameter_links)
        );
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );

        let alias_links = fixture
            .store
            .type_alias_links(function_alias)
            .unwrap()
            .clone();
        assert!(
            fixture
                .store
                .set_type_alias_links(function_alias, TypeAliasLinks::default())
        );
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        assert!(
            fixture
                .store
                .set_type_alias_links(function_alias, alias_links)
        );
        assert_eq!(
            fixture.store.validate_union_constituent(function_type),
            Ok(())
        );

        let maybe = query_declared(
            &mut fixture,
            maybe_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        assert!(union_types(&fixture.store, maybe).contains(&function_type));
        assert!(
            union_types(&fixture.store, maybe)
                .contains(&fixture.store.intrinsic_bootstrap().unwrap().undefined_type)
        );

        let function_symbol = node_symbol(&fixture, function);
        assert!(
            fixture
                .store
                .set_symbol_declarations(function_symbol, None, None)
        );
        assert!(fixture.store.set_structured_type_members(
            function_type,
            None,
            None,
            None,
            None,
            None,
        ));
        assert!(matches!(
            fixture.store.validate_union_constituent(function_type),
            Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == function_type
        ));
        let erased = function_store_state(&fixture.store);
        assert_eq!(
            query_empty_host_declared(&mut fixture, function_alias, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(function_type)
            ))
        );
        assert_eq!(function_store_state(&fixture.store), erased);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn source_callable_query_materializes_both_families_and_shared_consumers() {
        let source = concat!(
            "type Target = (value: string, optional?: number) => boolean; ",
            "export function exported(value: string, optional?: number): boolean { return true; } ",
            "const arrow = (value: string, optional?: number): boolean => true;",
        );
        let mut fixture = fixture_with_options(
            source,
            CanonicalModuleState::External,
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            |_| {},
        );
        let declaration = named_node(&fixture, SyntaxKind::FunctionDeclaration, "exported");
        let arrow = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .expect("source has one arrow function");
        let (owner, export_local, arrow_owner) = {
            let bound = fixture.files.get(&fixture.file).unwrap();
            (
                bound.symbol(declaration).unwrap(),
                bound.local_symbol(declaration).unwrap(),
                bound.symbol(arrow).unwrap(),
            )
        };
        assert!(fixture.store.symbol(owner).unwrap().parent().is_some());
        assert!(
            fixture
                .store
                .symbol(export_local)
                .unwrap()
                .value_declaration()
                .is_none(),
            "direct-export locals are EXPORT_VALUE markers, not value declarations",
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declaration_type =
            query_source_callable(&mut fixture, declaration, owner, &mut diagnostics).unwrap();
        let arrow_type =
            query_source_callable(&mut fixture, arrow, arrow_owner, &mut diagnostics).unwrap();
        assert_ne!(declaration_type, arrow_type);
        assert_eq!(
            fixture
                .store
                .source_callable_provenance(declaration_type)
                .unwrap()
                .family,
            SourceCallableFamily::FunctionDeclaration,
        );
        assert_eq!(
            fixture
                .store
                .source_callable_provenance(arrow_type)
                .unwrap()
                .family,
            SourceCallableFamily::ArrowFunction,
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, declaration_type),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, arrow_type),
            StoredSourceCallableValidation::Valid(_)
        ));

        let declaration_signature = function_signature(&fixture.store, declaration);
        let arrow_signature = function_signature(&fixture.store, arrow);
        for signature_id in [declaration_signature, arrow_signature] {
            let signature = fixture.store.signature(signature_id).unwrap();
            assert_eq!(signature.min_argument_count(), 1);
            let [required, optional] = signature.parameters() else {
                panic!("source callable has two parameters")
            };
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(*required)
                    .unwrap()
                    .resolved_type,
                Some(bootstrap.string_type),
            );
            let optional_type = fixture
                .store
                .value_symbol_links(*optional)
                .unwrap()
                .resolved_type
                .unwrap();
            assert!(union_types(&fixture.store, optional_type).contains(&bootstrap.number_type));
            assert!(union_types(&fixture.store, optional_type).contains(&bootstrap.undefined_type));
            assert!(signature.resolved_return_type().is_none());
        }

        let before_warm = (
            function_store_state(&fixture.store),
            fixture.store.source_callable_provenance_lengths(),
        );
        assert_eq!(
            query_source_callable(&mut fixture, declaration, owner, &mut diagnostics),
            Ok(declaration_type),
        );
        assert_eq!(
            (
                function_store_state(&fixture.store),
                fixture.store.source_callable_provenance_lengths(),
            ),
            before_warm,
        );

        let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
        assert_eq!(
            query_signature_return(&mut fixture, declaration_signature, &mut diagnostics),
            Ok(boolean),
        );
        let resolved_return_state = function_store_state(&fixture.store);
        assert_eq!(
            query_signature_return(&mut fixture, declaration_signature, &mut diagnostics),
            Ok(boolean),
        );
        assert_eq!(function_store_state(&fixture.store), resolved_return_state);
        assert_eq!(
            query_signature_return(&mut fixture, arrow_signature, &mut diagnostics),
            Ok(boolean),
        );

        let displayed = {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            type_to_string_with_host_and_flags(
                &fixture.store,
                &host,
                declaration_type,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )
        };
        assert_eq!(
            displayed.as_deref(),
            Ok("(value: string, optional?: number | undefined) => boolean"),
        );

        let target_symbol = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Target");
        let target = query_declared(
            &mut fixture,
            target_symbol,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let target_node = function_type_node(&fixture, "Target");
        let target_signature = function_signature(&fixture.store, target_node);
        query_signature_return(&mut fixture, target_signature, &mut diagnostics).unwrap();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(declaration_type, target, true,),
            Ok(true),
        );
        let optional = fixture
            .store
            .signature(declaration_signature)
            .unwrap()
            .parameters()[1];
        let expected_optional = fixture
            .store
            .value_symbol_links(optional)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(declaration_signature)
                .and_then(|types| types.get(1))
                .copied(),
            Some(expected_optional),
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_ne!(expected_optional, number);
        assert!(fixture.store.set_value_symbol_links(
            optional,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            validate_stored_source_callable(&fixture.store, declaration_type),
            StoredSourceCallableValidation::Malformed,
        );
        assert!(matches!(
            validate_stored_single_callable(&fixture.store, declaration_type),
            StoredSingleCallableValidation::Malformed {
                family: CallableFamily::FunctionDeclaration
            }
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn stored_source_callable_rejects_export_route_and_owner_parent_corruption() {
        let mut fixture = fixture_with_options(
            "export function exported(value: string): boolean { return true; }",
            CanonicalModuleState::External,
            IntrinsicBootstrapOptions::default(),
            |_| {},
        );
        let declaration = named_node(&fixture, SyntaxKind::FunctionDeclaration, "exported");
        let (owner, export_local) = {
            let bound = fixture.files.get(&fixture.file).unwrap();
            (
                bound.symbol(declaration).unwrap(),
                bound.local_symbol(declaration).unwrap(),
            )
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ =
            query_source_callable(&mut fixture, declaration, owner, &mut diagnostics).unwrap();
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(fixture.store.set_symbol_declarations(
            export_local,
            Some(vec![declaration]),
            Some(declaration),
        ));
        assert_eq!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Malformed,
        );
        assert!(matches!(
            validate_stored_single_callable(&fixture.store, type_),
            StoredSingleCallableValidation::Malformed {
                family: CallableFamily::FunctionDeclaration
            }
        ));
        assert!(
            fixture
                .store
                .set_symbol_declarations(export_local, Some(vec![declaration]), None,)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(
            fixture
                .store
                .set_symbol_relationships(owner, None, None, None, None)
        );
        assert_eq!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Malformed,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn zero_parameter_callables_publish_explicit_empty_parameter_provenance() {
        let mut fixture = fixture_with_module_state(
            "type EmptyType = () => string; function empty(): string { return ''; }",
            CanonicalModuleState::External,
        );
        let source_declaration = named_node(&fixture, SyntaxKind::FunctionDeclaration, "empty");
        let source_owner = node_symbol(&fixture, source_declaration);
        let function_node = function_type_node(&fixture, "EmptyType");
        let function_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "EmptyType");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let source_type = query_source_callable(
            &mut fixture,
            source_declaration,
            source_owner,
            &mut diagnostics,
        )
        .unwrap();
        let function_type = query_declared(
            &mut fixture,
            function_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        for signature in [
            function_signature(&fixture.store, source_declaration),
            function_signature(&fixture.store, function_node),
        ] {
            assert_eq!(
                fixture.store.callable_signature_parameter_types(signature),
                Some(&[][..]),
            );
        }
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, source_type),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(matches!(
            functions::validate_stored_function_type(&fixture.store, function_type),
            functions::StoredFunctionTypeValidation::Valid(_)
        ));
        assert_eq!(fixture.store.callable_signature_parameter_types_len(), 2);
        assert!(diagnostics.is_empty());
    }
}
