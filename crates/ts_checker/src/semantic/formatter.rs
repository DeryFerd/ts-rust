//! Dependency-closed canonical semantic type display.
//!
//! This is the primitive, literal, canonical-union, global-array, empty-tuple,
//! property-only object, and exact annotated function-type prefix of pinned
//! `internal/checker/printer.go::typeToString`,
//! `internal/checker/nodebuilderimpl.go::typeToTypeNode`, and
//! `internal/checker/relater.go::reportRelationError` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. It deliberately stops before
//! qualified symbol naming and advanced structural type serialization. Those
//! families return [`TypeDisplayUnavailable`] rather than placeholder text.

use std::{collections::HashSet, fmt::Write as _, ops};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags, canonical_has_syntactic_modifier,
};

use super::{
    ArrayTypeError, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost,
    DeclaredTypeHostError, EmptyTupleTypeError, IndexInfoId, SignatureId, TypeAliasId, TypeId,
    bootstrap::LiteralTypeCacheError,
    callables::{
        CallableFamily, SingleCallableDisplayError, StoredSingleCallableValidation,
        ValidatedSingleCallSignatureDisplay, single_callable_display_projection,
        single_callable_family, validate_stored_single_callable,
    },
    declared::cached_ordinary_type_parameter_owner,
    derived_types::DerivedObjectLiteralValidation,
    enums,
    functions::{FunctionTypeDisplayError, FunctionTypeUnsupported},
    keyof_types,
    links::ValueSymbolLinks,
    object_members,
    reference_types::validate_direct_generic_reference,
    signatures::IndexFlags,
    source_callables::{SourceCallableDisplayError, SourceCallableUnsupported},
    structured_members::{InterfaceHeritageMembersValidation, validate_interface_heritage_members},
    type_records::{
        LiteralTypeData, LiteralValue, TypeCacheState, TypeData, TypeDataKind, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

const DEFAULT_MAXIMUM_TRUNCATION_LENGTH: usize = 160;
const NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH: usize = 1_000_000;
const ELLIPSIS: &str = "...";

/// The pinned `TypeFormatFlags` subset observable for dependency-closed
/// primitive, literal, canonical-union, property-only object, and exact
/// annotated function-type display.
///
/// Numeric values intentionally match typescript-go. Unsupported flag
/// families are absent rather than silently ignored.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct CanonicalTypeFormatFlags(u32);

impl CanonicalTypeFormatFlags {
    pub const NONE: Self = Self(0);
    /// Do not use the ordinary 160-unit node-builder budget. The pinned hard
    /// output cutoff still applies at two million bytes.
    pub const NO_TRUNCATION: Self = Self(1 << 0);
    /// Permit an alias defined outside the current scope to retain its name.
    /// Context-free formatting has no enclosing declaration, so canonical
    /// unqualified union aliases are accessible with or without this flag.
    pub const USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE: Self = Self(1 << 14);
    /// Permit the context-free `unique symbol` representation.
    pub const ALLOW_UNIQUE_ES_SYMBOL_TYPE: Self = Self(1 << 20);
    /// Prefer single quotes for synthesized string literal type nodes.
    pub const USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE: Self = Self(1 << 28);

    // `checker.(*Checker).typeToString` supplies this exact pair at the pinned
    // revision. Keep the wrapper default distinct from explicit `NONE`.
    pub(super) const TYPE_TO_STRING_DEFAULT: Self =
        Self(Self::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.0 | Self::ALLOW_UNIQUE_ES_SYMBOL_TYPE.0);

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }
}

impl ops::BitOr for CanonicalTypeFormatFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl ops::BitOrAssign for CanonicalTypeFormatFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// A function-shaped display family outside the installed exact signature
/// cut. These cases stay distinct so callers never mistake a synthesized
/// fallback for canonical TypeScript text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FunctionTypeDisplayUnavailable {
    SourceContext,
    GenericAlias,
    GenericSignature,
    ThisParameter,
    RestParameter,
    InitializedParameter,
    DestructuredParameter,
    ParameterModifiers,
    MissingParameterType,
    MissingReturnType,
    PendingSignature,
    UnresolvedReturn,
    TypePredicate,
    Overloads,
    ConstructSignatures,
    IndexSignatures,
    CallableProperties,
    UnvalidatedCallable,
}

/// A canonical type or display dependency outside the installed formatter
/// prefix. No variant contains substitute display text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeDisplayUnavailable {
    Type(TypeId),
    Alias {
        type_id: TypeId,
        alias: TypeAliasId,
    },
    UnsupportedType {
        type_id: TypeId,
        kind: TypeDataKind,
    },
    MalformedType(TypeId),
    InvalidUnion(TypeId),
    InvalidIntersection(TypeId),
    UnsupportedUnionConstituent {
        union: TypeId,
        constituent: TypeId,
    },
    CyclicType(TypeId),
    InvalidLiteralLinks(TypeId),
    UniqueSymbolName(TypeId),
    MissingBootstrap,
    ArrayType(ArrayTypeError),
    EmptyTupleType(EmptyTupleTypeError),
    FullyQualifiedName {
        source: TypeId,
        target: TypeId,
    },
    FunctionType {
        type_id: TypeId,
        reason: FunctionTypeDisplayUnavailable,
    },
    SourceHost(DeclaredTypeHostError),
    Utf8TruncationBoundary {
        type_id: TypeId,
        boundary: usize,
    },
}

impl std::fmt::Display for TypeDisplayUnavailable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Type(type_id) => write!(formatter, "type {type_id:?} is not store-owned"),
            Self::Alias { type_id, alias } => write!(
                formatter,
                "type {type_id:?} requires unavailable alias display for {alias:?}"
            ),
            Self::UnsupportedType { type_id, kind } => write!(
                formatter,
                "type {type_id:?} has unsupported display family {kind:?}"
            ),
            Self::MalformedType(type_id) => {
                write!(formatter, "type {type_id:?} has an invalid display payload")
            }
            Self::InvalidUnion(type_id) => {
                write!(
                    formatter,
                    "type {type_id:?} is not a canonical display union"
                )
            }
            Self::InvalidIntersection(type_id) => write!(
                formatter,
                "type {type_id:?} is not a canonical display intersection"
            ),
            Self::UnsupportedUnionConstituent { union, constituent } => write!(
                formatter,
                "union {union:?} contains unsupported display constituent {constituent:?}"
            ),
            Self::CyclicType(type_id) => {
                write!(formatter, "type {type_id:?} has a cyclic display graph")
            }
            Self::InvalidLiteralLinks(type_id) => write!(
                formatter,
                "literal type {type_id:?} has invalid fresh/regular links"
            ),
            Self::UniqueSymbolName(type_id) => write!(
                formatter,
                "unique symbol type {type_id:?} requires symbol-aware display"
            ),
            Self::MissingBootstrap => {
                formatter.write_str("literal relation display requires intrinsic checker bootstrap")
            }
            Self::ArrayType(error) => error.fmt(formatter),
            Self::EmptyTupleType(error) => error.fmt(formatter),
            Self::FullyQualifiedName { source, target } => write!(
                formatter,
                "types {source:?} and {target:?} require symbol-aware fully qualified display"
            ),
            Self::FunctionType { type_id, reason } => write!(
                formatter,
                "function-shaped type {type_id:?} has unavailable display dependency {reason:?}"
            ),
            Self::SourceHost(error) => error.fmt(formatter),
            Self::Utf8TruncationBoundary { type_id, boundary } => write!(
                formatter,
                "pinned byte truncation for {type_id:?} splits UTF-8 at byte {boundary}"
            ),
        }
    }
}

impl std::error::Error for TypeDisplayUnavailable {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ArrayType(error) => Some(error),
            Self::EmptyTupleType(error) => Some(error),
            Self::SourceHost(error) => Some(error),
            _ => None,
        }
    }
}

/// Exact source and target arguments for the ordinary TS2322 relation error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignabilityErrorDisplay {
    pub source: String,
    pub target: String,
}

/// Pinned context-free `TypeToString` for the installed display prefix.
///
/// This preserves the supplied type identity. In particular, fresh literals
/// remain literal text; relation-diagnostic widening belongs to
/// [`get_type_names_for_assignability_error`].
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] for a foreign or malformed type, or when
/// exact display needs an alias or type family outside the installed prefix.
pub fn type_to_string(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_flags(
        store,
        type_id,
        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
    )
}

/// Pinned context-free `TypeToStringEx` behavior for flags observable in the
/// installed primitive/literal/canonical-union/property-object/function prefix.
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] instead of synthesizing placeholder
/// text when the exact display dependency is not installed.
pub fn type_to_string_with_flags(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_optional_context_and_flags(store, None, None, type_id, flags)
}

/// Global-aware `TypeToString` for canonical `Array<T>` and
/// `ReadonlyArray<T>` references in addition to the ordinary installed
/// formatter prefix.
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] when the type or authoritative global
/// identities are malformed, or the exact display family is unavailable.
pub fn type_to_string_with_global_types(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    type_id: TypeId,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_global_types_and_flags(
        store,
        global_types,
        type_id,
        CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
    )
}

/// Flag-aware form of [`type_to_string_with_global_types`].
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] under the same conditions as the
/// default global-aware query.
pub fn type_to_string_with_global_types_and_flags(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_optional_context_and_flags(store, None, Some(global_types), type_id, flags)
}

/// Host-aware form used by source-backed checker paths once they already own
/// a validated declared-type view. The host proves source-backed owners such
/// as exported interfaces and structural type literals whose `readonly`
/// modifiers are not retained by binder-owned symbol records.
#[allow(dead_code)] // Source/production wiring is owned by the next integration slice.
pub(super) fn type_to_string_with_host_and_flags(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_optional_context_and_flags(store, Some(host), None, type_id, flags)
}

pub(super) fn type_to_string_with_host_global_types_and_flags(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    type_to_string_with_optional_context_and_flags(
        store,
        Some(host),
        Some(global_types),
        type_id,
        flags,
    )
}

fn type_to_string_with_optional_context_and_flags(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    let mut state = DisplayState::default();
    let mut visiting = HashSet::new();
    let displayed = display_type_worker(
        store,
        host,
        global_types,
        type_id,
        flags,
        &mut state,
        &mut visiting,
    )?;
    truncate_display(type_id, displayed, flags)
}

/// Pinned TS2322 source/target display arguments from
/// `getTypeNamesForErrorDisplay` plus the literal-source generalization in
/// `reportRelationError`.
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] when either type or the exact
/// fully-qualified/generalized representation falls outside this formatter.
pub fn get_type_names_for_assignability_error(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_flags(
        store,
        source,
        target,
        CanonicalTypeFormatFlags::NONE,
    )
}

/// Flag-aware form of [`get_type_names_for_assignability_error`]. The pinned
/// relation path starts from ordinary `TypeToString`, so unique-symbol display
/// remains enabled in addition to the caller's observable formatting flags.
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] for the same reasons as the default
/// helper.
pub fn get_type_names_for_assignability_error_with_flags(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_optional_host_and_flags(
        store, None, None, source, target, flags,
    )
}

/// Global-aware TS2322 source and target display arguments.
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] when either type or an authoritative
/// global-array identity is malformed or outside the installed prefix.
pub fn get_type_names_for_assignability_error_with_global_types(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    source: TypeId,
    target: TypeId,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_global_types_and_flags(
        store,
        global_types,
        source,
        target,
        CanonicalTypeFormatFlags::NONE,
    )
}

/// Flag-aware form of
/// [`get_type_names_for_assignability_error_with_global_types`].
///
/// # Errors
///
/// Returns [`TypeDisplayUnavailable`] under the same conditions as the
/// default global-aware query.
pub fn get_type_names_for_assignability_error_with_global_types_and_flags(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    source: TypeId,
    target: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_optional_host_and_flags(
        store,
        None,
        Some(global_types),
        source,
        target,
        flags,
    )
}

/// Host-aware TS2322 display pair for source-backed checker paths. Keeping the
/// host on the pair query prevents source and target from being formatted with
/// different provenance rules.
#[allow(dead_code)] // Source/production wiring is owned by the next integration slice.
pub(super) fn get_type_names_for_assignability_error_with_host_and_flags(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    source: TypeId,
    target: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_optional_host_and_flags(
        store,
        Some(host),
        None,
        source,
        target,
        flags,
    )
}

pub(super) fn get_type_names_for_assignability_error_with_host_global_types_and_flags(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source: TypeId,
    target: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    get_type_names_for_assignability_error_with_optional_host_and_flags(
        store,
        Some(host),
        Some(global_types),
        source,
        target,
        flags,
    )
}

fn get_type_names_for_assignability_error_with_optional_host_and_flags(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    source: TypeId,
    target: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
    let flags = flags | CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    let source_record = store
        .type_payload(source)
        .ok_or(TypeDisplayUnavailable::Type(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(TypeDisplayUnavailable::Type(target))?;
    let mut source_name =
        type_to_string_with_optional_context_and_flags(store, host, global_types, source, flags)?;
    let target_name =
        type_to_string_with_optional_context_and_flags(store, host, global_types, target, flags)?;

    // The pinned fallback asks for fully qualified names when the ordinary
    // strings collide. Primitive/literal names are invariant under that flag.
    // Unique symbols instead need symbol accessibility and `typeof` naming,
    // which this context-free prefix intentionally does not guess.
    if source_name == target_name
        && (source_record
            .flags()
            .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
            || target_record
                .flags()
                .intersects(TypeFlags::UNIQUE_ES_SYMBOL))
    {
        return Err(TypeDisplayUnavailable::FullyQualifiedName { source, target });
    }

    if !target_record.flags().intersects(TypeFlags::NEVER)
        && is_literal_type(source_record)
        && !type_could_have_top_level_singleton_types(store, target, &mut HashSet::new())?
    {
        let generalized = base_type_of_literal_type(store, source, source_record)?;
        let generalized_record = store
            .type_payload(generalized)
            .ok_or(TypeDisplayUnavailable::Type(generalized))?;
        if generalized_record
            .flags()
            .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
        {
            // `reportRelationError` switches to `getTypeNameForErrorDisplay`
            // here. Without AllowUniqueESSymbolType, an exact result depends on
            // value-symbol accessibility and can be `typeof <name>`.
            return Err(TypeDisplayUnavailable::UniqueSymbolName(generalized));
        }
        source_name = type_to_string_with_optional_context_and_flags(
            store,
            host,
            global_types,
            generalized,
            flags,
        )?;
    }

    Ok(AssignabilityErrorDisplay {
        source: source_name,
        target: target_name,
    })
}

fn display_type_worker(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_id)
        .ok_or(TypeDisplayUnavailable::Type(type_id))?;
    let type_flags = record.flags();

    if store.canonical_empty_tuple_type_cache() == Some(type_id) {
        store
            .validate_canonical_empty_tuple_type(type_id)
            .map_err(TypeDisplayUnavailable::EmptyTupleType)?;
        state.add(2);
        return Ok("[]".to_owned());
    }

    if type_flags.intersects(TypeFlags::ANY) {
        if let Some(alias) = record.alias() {
            return Err(TypeDisplayUnavailable::Alias { type_id, alias });
        }
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        if let Some(bootstrap) = store.intrinsic_bootstrap() {
            if type_id == bootstrap.unresolved_type {
                return Ok("/*unresolved*/ any".to_owned());
            }
            if type_id == bootstrap.intrinsic_marker_type {
                state.add(3);
                return Ok("intrinsic".to_owned());
            }
        }
        state.add(3);
        return Ok("any".to_owned());
    }
    if type_flags.intersects(TypeFlags::UNKNOWN) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("unknown".to_owned());
    }
    if type_flags.intersects(TypeFlags::STRING) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(6);
        return Ok("string".to_owned());
    }
    if type_flags.intersects(TypeFlags::NUMBER) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(6);
        return Ok("number".to_owned());
    }
    if type_flags.intersects(TypeFlags::BIG_INT) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(6);
        return Ok("bigint".to_owned());
    }
    if type_flags.intersects(TypeFlags::BOOLEAN) && record.alias().is_none() {
        require_data_kind(type_id, record, TypeDataKind::Union)?;
        validate_display_union(store, global_types, type_id)?;
        state.add(7);
        return Ok("boolean".to_owned());
    }
    if type_flags.intersects(TypeFlags::ENUM_LIKE) {
        let name = enums::enum_type_display_name(store, type_id)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        state.add(name.len());
        return Ok(name);
    }
    if type_flags.intersects(TypeFlags::STRING_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::String(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        let quote = if flags
            .contains(CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE)
        {
            '\''
        } else {
            '"'
        };
        state.add(value.len().saturating_add(2));
        return Ok(quote_string_literal(value, quote));
    }
    if type_flags.intersects(TypeFlags::NUMBER_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::Number(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        let value = value.to_string();
        state.add(value.len());
        return Ok(value);
    }
    if type_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::BigInt(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        let value = format!("{value}n");
        state.add(value.len());
        return Ok(value);
    }
    if type_flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::Boolean(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        state.add(if *value { 4 } else { 5 });
        return Ok(value.to_string());
    }
    if type_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
        require_data_kind(type_id, record, TypeDataKind::UniqueEsSymbol)?;
        if !flags.contains(CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE) {
            return Err(TypeDisplayUnavailable::UniqueSymbolName(type_id));
        }
        state.add(13);
        return Ok("unique symbol".to_owned());
    }
    if type_flags.intersects(TypeFlags::VOID) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(4);
        return Ok("void".to_owned());
    }
    if type_flags.intersects(TypeFlags::UNDEFINED) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(9);
        return Ok("undefined".to_owned());
    }
    if type_flags.intersects(TypeFlags::NULL) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(4);
        return Ok("null".to_owned());
    }
    if type_flags.intersects(TypeFlags::NEVER) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(5);
        return Ok("never".to_owned());
    }
    if type_flags.intersects(TypeFlags::ES_SYMBOL) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(6);
        return Ok("symbol".to_owned());
    }
    if type_flags.intersects(TypeFlags::NON_PRIMITIVE) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        state.add(6);
        return Ok("object".to_owned());
    }
    if type_flags.intersects(TypeFlags::TYPE_PARAMETER) {
        require_data_kind(type_id, record, TypeDataKind::TypeParameter)?;
        let symbol = cached_ordinary_type_parameter_owner(store, type_id)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        return display_symbol_name(store, type_id, symbol, state)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id));
    }
    if type_flags.intersects(TypeFlags::INDEX) {
        return display_index_type(store, host, global_types, type_id, flags, state, visiting);
    }
    if type_flags.intersects(TypeFlags::UNION) {
        return display_union_type(store, host, global_types, type_id, flags, state, visiting);
    }
    if type_flags.intersects(TypeFlags::INTERSECTION) {
        return display_intersection_type(
            store,
            host,
            global_types,
            type_id,
            flags,
            state,
            visiting,
        );
    }
    if type_flags.intersects(TypeFlags::OBJECT) {
        return display_object_type(
            store,
            host,
            global_types,
            type_id,
            record,
            flags,
            state,
            visiting,
        );
    }
    if let Some(alias) = record.alias() {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    }
    Err(TypeDisplayUnavailable::UnsupportedType {
        type_id,
        kind: record.data().kind(),
    })
}

#[allow(clippy::too_many_arguments)]
fn display_index_type(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_id)
        .ok_or(TypeDisplayUnavailable::Type(type_id))?;
    let TypeData::Index(data) = record.data() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let target = store
        .type_payload(data.target)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if record.flags() != TypeFlags::INDEX
        || record.object_flags() != ObjectFlags::NONE
        || record.symbol().is_some()
        || record.alias().is_some()
        || data.index_flags != IndexFlags::NONE
        || !target.flags().intersects(TypeFlags::OBJECT)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    state.add(6);
    let result = match target.data() {
        TypeData::Interface(_) => display_interface_name(store, host, data.target, target, state),
        _ => display_type_worker(
            store,
            host,
            global_types,
            data.target,
            flags,
            state,
            visiting,
        ),
    }
    .map(|target| format!("keyof {target}"));
    visiting.remove(&type_id);
    result
}

#[derive(Default)]
struct DisplayState {
    approximate_length: usize,
    truncating: bool,
}

impl DisplayState {
    fn add(&mut self, amount: usize) {
        self.approximate_length = self.approximate_length.saturating_add(amount);
    }

    fn check_truncation(&mut self, flags: CanonicalTypeFormatFlags) -> bool {
        if self.truncating {
            return true;
        }
        let maximum = if flags.contains(CanonicalTypeFormatFlags::NO_TRUNCATION) {
            NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH
        } else {
            DEFAULT_MAXIMUM_TRUNCATION_LENGTH
        };
        self.truncating = self.approximate_length > maximum;
        self.truncating
    }
}

#[derive(Clone, Copy)]
enum StructuralObjectProof {
    Synthetic,
    ObjectLiteral,
    DeclaredTypeLiteral(SemanticSymbolId),
}

#[allow(clippy::too_many_arguments)]
fn display_object_type(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    record: &TypeRecord,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    if record.flags() != TypeFlags::OBJECT {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    if let Some(global_types) = global_types
        && let Some(array) = store
            .canonical_array_reference(global_types, type_id)
            .map_err(TypeDisplayUnavailable::ArrayType)?
    {
        return display_array_type(
            store,
            host,
            global_types,
            type_id,
            array.element_type,
            array.readonly,
            flags,
            state,
            visiting,
        );
    }
    if let Some(alias) = record.alias() {
        if single_callable_family(store, type_id).is_some() {
            validate_opaque_single_callable_alias(store, type_id)?;
        } else {
            validate_property_object_alias(store, host, type_id, record, alias)?;
        }
        return display_alias_name(store, type_id, alias, state);
    }
    if let Some(host) = host
        && record.object_flags().contains(ObjectFlags::REFERENCE)
        && matches!(
            record.data(),
            TypeData::TypeReference(_) | TypeData::Interface(_)
        )
    {
        return display_direct_generic_reference(
            store,
            host,
            global_types,
            type_id,
            flags,
            state,
            visiting,
        );
    }

    if let Some(projection) = validated_single_callable_display(store, host, global_types, type_id)?
    {
        if !visiting.insert(type_id) {
            return Err(TypeDisplayUnavailable::CyclicType(type_id));
        }
        let result = display_single_call_signature(
            store,
            host,
            global_types,
            &projection,
            flags,
            state,
            visiting,
        );
        visiting.remove(&type_id);
        return result;
    }
    if let Some(reason) = unsupported_callable_shape(store, type_id, record)? {
        return Err(TypeDisplayUnavailable::FunctionType { type_id, reason });
    }

    let kind = record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK;
    if kind == ObjectFlags::INTERFACE {
        return display_interface_name(store, host, type_id, record, state);
    }
    if kind != ObjectFlags::ANONYMOUS || !matches!(record.data(), TypeData::Object(_)) {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
    }

    let proof = validate_structural_object_shell(store, host, global_types, type_id, record)?;
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    let result = display_structural_properties(
        store,
        host,
        global_types,
        type_id,
        record,
        proof,
        flags,
        state,
        visiting,
    );
    visiting.remove(&type_id);
    result
}

#[allow(clippy::too_many_arguments)] // Keep recursive formatter state explicit.
fn display_direct_generic_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let reference = validate_direct_generic_reference(store, type_id)
        .map_err(|_| TypeDisplayUnavailable::MalformedType(type_id))?;
    let target = store
        .type_payload(reference.target)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let symbol = target
        .symbol()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [declaration] = symbol_record.declarations().unwrap_or_default() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let declaration_record = host
        .node(*declaration)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let name_node = match &declaration_record.data {
        NodeData::ClassDeclaration(class) => class
            .name
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?,
        NodeData::InterfaceDeclaration(interface) => interface.name,
        _ => return Err(TypeDisplayUnavailable::MalformedType(type_id)),
    };
    let name_node = NodeRef::new(declaration.arena, declaration.file, name_node);
    if !host.symbol_matches(store, *declaration, symbol)
        || !host.node(name_node).is_some_and(|node| {
            matches!(&node.data, NodeData::Identifier(name)
                if symbol_record.name().as_utf8() == Some(name.text.as_str()))
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    let result = (|| {
        let mut result = display_symbol_name(store, type_id, symbol, state)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        result.push('<');
        state.add(2);
        for (index, argument) in reference.type_arguments.iter().enumerate() {
            if index != 0 {
                result.push_str(", ");
                state.add(2);
            }
            result.push_str(&display_type_worker(
                store,
                Some(host),
                global_types,
                *argument,
                flags,
                state,
                visiting,
            )?);
        }
        result.push('>');
        Ok(result)
    })();
    visiting.remove(&type_id);
    result
}

fn validate_opaque_single_callable_alias(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<(), TypeDisplayUnavailable> {
    match validate_stored_single_callable(store, type_id) {
        StoredSingleCallableValidation::Valid {
            family: CallableFamily::FunctionType,
            ..
        } => Ok(()),
        StoredSingleCallableValidation::Pending {
            family: CallableFamily::FunctionType,
        } => Err(TypeDisplayUnavailable::FunctionType {
            type_id,
            reason: FunctionTypeDisplayUnavailable::PendingSignature,
        }),
        StoredSingleCallableValidation::NotCallable
        | StoredSingleCallableValidation::Malformed { .. }
        | StoredSingleCallableValidation::Pending { .. }
        | StoredSingleCallableValidation::Valid { .. } => {
            Err(TypeDisplayUnavailable::MalformedType(type_id))
        }
    }
}

fn validated_single_callable_display(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
) -> Result<Option<ValidatedSingleCallSignatureDisplay>, TypeDisplayUnavailable> {
    if single_callable_family(store, type_id).is_none() {
        return Ok(None);
    }
    let host = host.ok_or(TypeDisplayUnavailable::FunctionType {
        type_id,
        reason: FunctionTypeDisplayUnavailable::SourceContext,
    })?;
    single_callable_display_projection(store, host, type_id, global_types)
        .map_err(|error| callable_display_unavailable(type_id, error))
}

const fn callable_display_unavailable(
    type_id: TypeId,
    error: SingleCallableDisplayError,
) -> TypeDisplayUnavailable {
    match error {
        SingleCallableDisplayError::FunctionType(error) => {
            function_display_unavailable(type_id, error)
        }
        SingleCallableDisplayError::SourceCallable(error) => {
            source_callable_display_unavailable(type_id, error)
        }
    }
}

const fn source_callable_display_unavailable(
    type_id: TypeId,
    error: SourceCallableDisplayError,
) -> TypeDisplayUnavailable {
    let reason = match error {
        SourceCallableDisplayError::Unsupported(reason) => match reason {
            SourceCallableUnsupported::GenericSignature(_)
            | SourceCallableUnsupported::GenericInferredReturn(_) => {
                FunctionTypeDisplayUnavailable::GenericSignature
            }
            SourceCallableUnsupported::ThisParameter(_) => {
                FunctionTypeDisplayUnavailable::ThisParameter
            }
            SourceCallableUnsupported::RestParameterNotLast(_)
            | SourceCallableUnsupported::OptionalRestParameter(_)
            | SourceCallableUnsupported::AmbientRestParameter(_) => {
                FunctionTypeDisplayUnavailable::RestParameter
            }
            SourceCallableUnsupported::InitializedRestParameter(_)
            | SourceCallableUnsupported::OptionalInitializedParameter(_)
            | SourceCallableUnsupported::AmbientParameterInitializer(_) => {
                FunctionTypeDisplayUnavailable::InitializedParameter
            }
            SourceCallableUnsupported::DestructuredParameter(_) => {
                FunctionTypeDisplayUnavailable::DestructuredParameter
            }
            SourceCallableUnsupported::ParameterModifiers(_) => {
                FunctionTypeDisplayUnavailable::ParameterModifiers
            }
            SourceCallableUnsupported::MissingParameterType(_) => {
                FunctionTypeDisplayUnavailable::MissingParameterType
            }
            SourceCallableUnsupported::TypePredicate(_) => {
                FunctionTypeDisplayUnavailable::TypePredicate
            }
            SourceCallableUnsupported::OverloadDeclaration(_) => {
                FunctionTypeDisplayUnavailable::Overloads
            }
            SourceCallableUnsupported::Async(_)
            | SourceCallableUnsupported::Generator(_)
            | SourceCallableUnsupported::ExpandoProperties(_)
            | SourceCallableUnsupported::Modifiers(_)
            | SourceCallableUnsupported::RequiredAfterOptional(_) => {
                FunctionTypeDisplayUnavailable::UnvalidatedCallable
            }
        },
        SourceCallableDisplayError::Pending => FunctionTypeDisplayUnavailable::PendingSignature,
        SourceCallableDisplayError::Malformed => {
            return TypeDisplayUnavailable::MalformedType(type_id);
        }
    };
    TypeDisplayUnavailable::FunctionType { type_id, reason }
}

const fn function_display_unavailable(
    type_id: TypeId,
    error: FunctionTypeDisplayError,
) -> TypeDisplayUnavailable {
    let reason = match error {
        FunctionTypeDisplayError::Unsupported(reason) => match reason {
            FunctionTypeUnsupported::GenericAlias(_) => {
                FunctionTypeDisplayUnavailable::GenericAlias
            }
            FunctionTypeUnsupported::GenericSignature(_) => {
                FunctionTypeDisplayUnavailable::GenericSignature
            }
            FunctionTypeUnsupported::ThisParameter(_) => {
                FunctionTypeDisplayUnavailable::ThisParameter
            }
            FunctionTypeUnsupported::RestParameter(_) => {
                FunctionTypeDisplayUnavailable::RestParameter
            }
            FunctionTypeUnsupported::InitializedParameter(_) => {
                FunctionTypeDisplayUnavailable::InitializedParameter
            }
            FunctionTypeUnsupported::DestructuredParameter(_) => {
                FunctionTypeDisplayUnavailable::DestructuredParameter
            }
            FunctionTypeUnsupported::ParameterModifiers(_) => {
                FunctionTypeDisplayUnavailable::ParameterModifiers
            }
            FunctionTypeUnsupported::MissingParameterType(_) => {
                FunctionTypeDisplayUnavailable::MissingParameterType
            }
            FunctionTypeUnsupported::MissingReturnType(_) => {
                FunctionTypeDisplayUnavailable::MissingReturnType
            }
        },
        FunctionTypeDisplayError::Pending => FunctionTypeDisplayUnavailable::PendingSignature,
        FunctionTypeDisplayError::Malformed => {
            return TypeDisplayUnavailable::MalformedType(type_id);
        }
    };
    TypeDisplayUnavailable::FunctionType { type_id, reason }
}

fn unsupported_callable_shape(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    record: &TypeRecord,
) -> Result<Option<FunctionTypeDisplayUnavailable>, TypeDisplayUnavailable> {
    let Some(structured) = record.data().structured() else {
        return Ok(None);
    };
    let signatures = structured.signatures.as_deref().unwrap_or_default();
    if structured.call_signature_count > signatures.len() {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let has_indexes = structured
        .index_infos
        .as_ref()
        .is_some_and(|indexes| !indexes.is_empty());
    if signatures.is_empty() && structured.call_signature_count == 0 && !has_indexes {
        return Ok(None);
    }
    validate_unbranded_callable_cache(store, type_id, record, signatures)?;
    if structured
        .properties
        .as_ref()
        .is_some_and(|properties| !properties.is_empty())
    {
        return Ok(Some(FunctionTypeDisplayUnavailable::CallableProperties));
    }
    if has_indexes {
        return Ok(Some(FunctionTypeDisplayUnavailable::IndexSignatures));
    }
    if structured.call_signature_count > 1 {
        return Ok(Some(FunctionTypeDisplayUnavailable::Overloads));
    }
    if signatures.len() > structured.call_signature_count {
        return Ok(Some(FunctionTypeDisplayUnavailable::ConstructSignatures));
    }
    let signature_records = signatures
        .iter()
        .map(|signature| {
            store
                .signature(*signature)
                .ok_or(TypeDisplayUnavailable::MalformedType(type_id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if signature_records
        .iter()
        .any(|signature| !signature.type_parameters().is_empty())
    {
        return Ok(Some(FunctionTypeDisplayUnavailable::GenericSignature));
    }
    if signature_records
        .iter()
        .any(|signature| signature.this_parameter().is_some())
    {
        return Ok(Some(FunctionTypeDisplayUnavailable::ThisParameter));
    }
    if signature_records
        .iter()
        .any(|signature| signature.has_rest_parameter())
    {
        return Ok(Some(FunctionTypeDisplayUnavailable::RestParameter));
    }
    if signature_records
        .iter()
        .any(|signature| signature.resolved_type_predicate().is_some())
    {
        return Ok(Some(FunctionTypeDisplayUnavailable::TypePredicate));
    }
    Ok(Some(FunctionTypeDisplayUnavailable::UnvalidatedCallable))
}

fn validate_unbranded_callable_cache(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    record: &TypeRecord,
    signatures: &[SignatureId],
) -> Result<(), TypeDisplayUnavailable> {
    let structured = record
        .data()
        .structured()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if record.flags() != TypeFlags::OBJECT
        || !record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        || structured.call_signature_count > signatures.len()
        || structured
            .constrained
            .resolved_base_constraint
            .is_some_and(|constraint| store.type_payload(constraint).is_none())
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some_and(|cached| store.type_payload(cached).is_none())
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }

    for (index, signature) in signatures.iter().enumerate() {
        validate_unbranded_signature_record(store, type_id, *signature)?;
        let construct = index >= structured.call_signature_count;
        if store.signature(*signature).is_none_or(|signature| {
            signature
                .flags()
                .contains(super::signatures::SignatureFlags::CONSTRUCT)
                != construct
        }) {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
    }

    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    let mut unique_indexes = HashSet::with_capacity(indexes.len());
    for index in indexes {
        if !unique_indexes.insert(*index) {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        let record = store
            .index_info(*index)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        if store.type_payload(record.key_type()).is_none()
            || store.type_payload(record.value_type()).is_none()
            || record
                .declaration()
                .is_some_and(|declaration| !store.contains_node_ref(declaration))
            || record
                .index_symbol()
                .is_some_and(|symbol| store.symbol(symbol).is_none())
            || record
                .components()
                .iter()
                .any(|component| !store.contains_node_ref(*component))
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
    }
    let properties = structured.properties.as_deref().unwrap_or_default();
    validate_callable_member_table(
        store,
        type_id,
        record.symbol(),
        structured.members,
        properties,
        &signatures[..structured.call_signature_count],
        &signatures[structured.call_signature_count..],
        indexes,
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_callable_member_table(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    owner: Option<SemanticSymbolId>,
    members: Option<ts_binder::SymbolTableId>,
    properties: &[SemanticSymbolId],
    call_signatures: &[SignatureId],
    construct_signatures: &[SignatureId],
    indexes: &[IndexInfoId],
) -> Result<(), TypeDisplayUnavailable> {
    let property_set = properties.iter().copied().collect::<HashSet<_>>();
    if property_set.len() != properties.len()
        || owner.is_some_and(|owner| store.symbol(owner).is_none())
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let Some(members) = members else {
        return if properties.is_empty() {
            Ok(())
        } else {
            Err(TypeDisplayUnavailable::MalformedType(type_id))
        };
    };
    let table = store
        .symbol_table(members)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    for property in properties {
        let property_record = store
            .symbol(*property)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        if property_record.name().is_reserved_member_name()
            || table.get(property_record.name()) != Some(*property)
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
    }

    let call = table.get(InternalSymbolName::Call.as_ref());
    let construct = table.get(InternalSymbolName::New.as_ref());
    let index = table.get(InternalSymbolName::Index.as_ref());
    let reserved_count = usize::from(call.is_some())
        .saturating_add(usize::from(construct.is_some()))
        .saturating_add(usize::from(index.is_some()));
    if table.len() != properties.len().saturating_add(reserved_count)
        || table.iter().any(|(name, symbol)| {
            if name == InternalSymbolName::Call.as_ref()
                || name == InternalSymbolName::New.as_ref()
                || name == InternalSymbolName::Index.as_ref()
            {
                return false;
            }
            name.is_reserved_member_name()
                || !property_set.contains(&symbol)
                || store
                    .symbol(symbol)
                    .is_none_or(|symbol| symbol.name() != name)
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }

    validate_reserved_signature_member(
        store,
        type_id,
        owner,
        InternalSymbolName::Call,
        call,
        call_signatures,
        &[SyntaxKind::CallSignature, SyntaxKind::FunctionType],
    )?;
    validate_reserved_signature_member(
        store,
        type_id,
        owner,
        InternalSymbolName::New,
        construct,
        construct_signatures,
        &[SyntaxKind::ConstructSignature, SyntaxKind::ConstructorType],
    )?;
    validate_reserved_index_member(store, type_id, owner, index, indexes)?;
    Ok(())
}

fn validate_reserved_signature_member(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    owner: Option<SemanticSymbolId>,
    name: InternalSymbolName,
    symbol: Option<SemanticSymbolId>,
    signatures: &[SignatureId],
    declaration_kinds: &[SyntaxKind],
) -> Result<(), TypeDisplayUnavailable> {
    let Some(symbol) = symbol else {
        return Ok(());
    };
    let symbol_record = validate_reserved_callable_symbol(store, type_id, owner, name, symbol)?;
    if signatures.is_empty() {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let Some(declarations) = symbol_record.declarations() else {
        return Ok(());
    };
    if declarations.is_empty()
        || declarations.iter().enumerate().any(|(index, declaration)| {
            declarations[..index].contains(declaration)
                || !declaration_kinds.contains(
                    &store
                        .source_node_kind(*declaration)
                        .unwrap_or(SyntaxKind::Unknown),
                )
                || !signatures.iter().any(|signature| {
                    store
                        .signature(*signature)
                        .is_some_and(|signature| signature.declaration() == Some(*declaration))
                })
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

fn validate_reserved_index_member(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    owner: Option<SemanticSymbolId>,
    symbol: Option<SemanticSymbolId>,
    indexes: &[IndexInfoId],
) -> Result<(), TypeDisplayUnavailable> {
    let Some(symbol) = symbol else {
        return Ok(());
    };
    let symbol_record = validate_reserved_callable_symbol(
        store,
        type_id,
        owner,
        InternalSymbolName::Index,
        symbol,
    )?;
    if indexes.is_empty() {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let Some(declarations) = symbol_record.declarations() else {
        return Ok(());
    };
    if declarations.is_empty()
        || declarations.iter().enumerate().any(|(index, declaration)| {
            declarations[..index].contains(declaration)
                || store.source_node_kind(*declaration) != Some(SyntaxKind::IndexSignature)
                || !indexes.iter().any(|index| {
                    store
                        .index_info(*index)
                        .is_some_and(|index| index.declaration() == Some(*declaration))
                })
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

fn validate_reserved_callable_symbol(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    owner: Option<SemanticSymbolId>,
    name: InternalSymbolName,
    symbol: SemanticSymbolId,
) -> Result<&ts_binder::semantic::Symbol, TypeDisplayUnavailable> {
    let record = store
        .symbol(symbol)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if record.flags() != SymbolFlags::SIGNATURE
        || record.check_flags() != CheckFlags::NONE
        || record.name() != name.as_ref()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != owner
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(record)
}

fn validate_unbranded_signature_record(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    signature: SignatureId,
) -> Result<(), TypeDisplayUnavailable> {
    let signature = store
        .signature(signature)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let parameter_count = signature.parameters().len();
    let minimum = usize::try_from(signature.min_argument_count())
        .ok()
        .filter(|minimum| *minimum <= parameter_count);
    let resolved_minimum = signature.resolved_min_argument_count();
    let allowed_flags = super::signatures::SignatureFlags::HAS_REST_PARAMETER
        | super::signatures::SignatureFlags::HAS_LITERAL_TYPES
        | super::signatures::SignatureFlags::CONSTRUCT
        | super::signatures::SignatureFlags::ABSTRACT
        | super::signatures::SignatureFlags::IS_INNER_CALL_CHAIN
        | super::signatures::SignatureFlags::IS_OUTER_CALL_CHAIN
        | super::signatures::SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
        | super::signatures::SignatureFlags::IS_NON_INFERRABLE
        | super::signatures::SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE;
    let parameters_unique = signature
        .parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature.parameters()[..index].contains(parameter));
    let type_parameters_unique = signature
        .type_parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature.type_parameters()[..index].contains(parameter));
    let composite_valid = signature.composite().is_none_or(|composite| {
        composite
            .signatures()
            .iter()
            .all(|constituent| store.signature(*constituent).is_some())
    });
    if signature.flags().bits() & !allowed_flags.bits() != 0
        || minimum.is_none()
        || resolved_minimum < -1
        || !signature.has_rest_parameter()
            && usize::try_from(resolved_minimum).is_ok_and(|minimum| minimum > parameter_count)
        || !parameters_unique
        || !type_parameters_unique
        || signature
            .declaration()
            .is_some_and(|declaration| !store.contains_node_ref(declaration))
        || signature
            .parameters()
            .iter()
            .any(|parameter| store.symbol(*parameter).is_none())
        || signature
            .type_parameters()
            .iter()
            .any(|parameter| store.type_payload(*parameter).is_none())
        || signature
            .this_parameter()
            .is_some_and(|parameter| store.symbol(parameter).is_none())
        || signature
            .resolved_return_type()
            .is_some_and(|return_type| store.type_payload(return_type).is_none())
        || signature
            .resolved_type_predicate()
            .is_some_and(|predicate| store.type_predicate(predicate).is_none())
        || signature
            .target()
            .is_some_and(|target| store.signature(target).is_none())
        || signature
            .mapper()
            .is_some_and(|mapper| store.mapper_payload(mapper).is_none())
        || signature
            .isolated_signature_type()
            .is_some_and(|isolated| store.type_payload(isolated).is_none())
        || !composite_valid
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn display_single_call_signature(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    projection: &ValidatedSingleCallSignatureDisplay,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    // Pinned `signatureToSignatureDeclarationHelper`: three units is the
    // minimum signature contribution, independent of the emitted punctuation.
    state.add(3);
    let mut result = String::from("(");
    for (index, parameter) in projection.parameters.iter().enumerate() {
        if index != 0 {
            result.push_str(", ");
        }
        result.push_str(&parameter.name);
        if parameter.optional {
            result.push('?');
        }
        result.push_str(": ");
        state.add(parameter.name.len().saturating_add(3));
        result.push_str(&display_type_worker(
            store,
            host,
            global_types,
            parameter.value_type,
            flags,
            state,
            visiting,
        )?);
    }
    result.push_str(") => ");
    let return_type = projection
        .return_type
        .ok_or(TypeDisplayUnavailable::FunctionType {
            type_id: projection.owner,
            reason: FunctionTypeDisplayUnavailable::UnresolvedReturn,
        })?;
    result.push_str(&display_type_worker(
        store,
        host,
        global_types,
        return_type,
        flags,
        state,
        visiting,
    )?);
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn display_array_type(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: &CanonicalGlobalTypes,
    type_id: TypeId,
    element_type: TypeId,
    readonly: bool,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    let result = (|| {
        let element_record = store
            .type_payload(element_type)
            .ok_or(TypeDisplayUnavailable::Type(element_type))?;
        let mut element = display_type_worker(
            store,
            host,
            Some(global_types),
            element_type,
            flags,
            state,
            visiting,
        )?;
        let union_parentheses =
            element_record.flags().intersects(TypeFlags::UNION) && element_record.alias().is_none();
        let function_parentheses = is_unaliased_single_callable_type(store, element_type);
        if union_parentheses || function_parentheses {
            element = format!("({element})");
        }
        if readonly {
            element.insert_str(0, "readonly ");
        }
        element.push_str("[]");
        Ok(element)
    })();
    visiting.remove(&type_id);
    result
}

fn display_interface_name(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    record: &TypeRecord,
    state: &mut DisplayState,
) -> Result<String, TypeDisplayUnavailable> {
    let TypeData::Interface(interface) = record.data() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let resolved =
        record.object_flags() == (ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED);
    if record.object_flags() != ObjectFlags::INTERFACE && !resolved
        || interface.all_type_parameters.is_some()
        || interface.outer_type_parameter_count != 0
        || interface.this_type.is_some()
        || interface.reference.resolved_type_arguments.is_some()
        || interface.reference.node.is_some()
        || interface.reference.object.target.is_some()
        || interface.reference.object.mapper.is_some()
        || interface.reference.object.instantiations != TypeCacheState::Unallocated
    {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
    }
    let symbol_id = record
        .symbol()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let symbol = store
        .symbol(symbol_id)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let declarations = symbol
        .declarations()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [declaration] = declarations else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    if store.get_merged_symbol(symbol_id) != Some(symbol_id)
        || symbol.flags() != SymbolFlags::INTERFACE
        || symbol.check_flags() != CheckFlags::NONE
        || symbol.value_declaration().is_some()
        || !valid_display_interface_owner(store, host, symbol_id, symbol, *declaration)
        || symbol.exports().is_some()
        || symbol.export_symbol().is_some()
        || store
            .declared_type_links(symbol_id)
            .is_none_or(|links| links.declared_type != Some(type_id))
        || store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    if resolved {
        if validate_resolved_named_interface(store, type_id, symbol_id, interface).is_err()
            && !keyof_types::plan_nongeneric_keyof_type(store, type_id).is_ok_and(|plan| {
                plan.proof() == object_members::DeclaredPropertyObjectProof::Interface
            })
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
    } else if interface != &super::type_records::InterfaceTypeData::default() {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    display_symbol_name(store, type_id, symbol_id, state)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))
}

fn valid_display_interface_owner(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    symbol_id: SemanticSymbolId,
    symbol: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
) -> bool {
    match (store.source_node_is_exported(declaration), symbol.parent()) {
        (Some(false), None) => true,
        (Some(true), Some(_)) => host.is_some_and(|host| {
            object_members::plan_interface(store, host, symbol_id)
                .is_ok_and(|plan| plan.node == declaration && plan.symbol == symbol_id)
        }),
        _ => false,
    }
}

fn validate_resolved_named_interface(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    owner: SemanticSymbolId,
    interface: &super::type_records::InterfaceTypeData,
) -> Result<(), TypeDisplayUnavailable> {
    match validate_interface_heritage_members(store, type_id) {
        InterfaceHeritageMembersValidation::Valid => return Ok(()),
        InterfaceHeritageMembersValidation::Malformed => {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        InterfaceHeritageMembersValidation::NotHeritage => {}
    }
    let structured = &interface.reference.object.structured;
    if !interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || !interface.declared_members_resolved
        || interface.declared_members != structured.members
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || structured.constrained.resolved_base_constraint.is_some()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || store
            .symbol(owner)
            .is_none_or(|symbol| symbol.members() != structured.members)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let properties = structured.properties.as_deref().unwrap_or_default();
    validate_structured_member_table(store, type_id, structured.members, properties)?;
    for property in properties {
        let record = store
            .symbol(*property)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let [declaration] = record.declarations().unwrap_or_default() else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        let links = store
            .value_symbol_links(*property)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let property_type = links
            .resolved_type
            .filter(|property_type| store.type_payload(*property_type).is_some())
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        if !record.flags().contains(SymbolFlags::PROPERTY)
            || record.flags().without(allowed_flags) != SymbolFlags::NONE
            || record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || record.parent() != Some(owner)
            || record.value_declaration() != Some(*declaration)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
    }
    Ok(())
}

fn validate_property_object_alias(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    record: &TypeRecord,
    alias: TypeAliasId,
) -> Result<(), TypeDisplayUnavailable> {
    let TypeData::Object(object) = record.data() else {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    };
    let allowed_flags = ObjectFlags::ANONYMOUS
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::FROM_TYPE_NODE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK != ObjectFlags::ANONYMOUS
        || !(record.object_flags() & !allowed_flags).is_empty()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    }

    let owner = record
        .symbol()
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    let owner_record = store
        .symbol(owner)
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    if store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags() != SymbolFlags::TYPE_LITERAL
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name() != InternalSymbolName::Type.as_ref()
        || owner_record.parent().is_some()
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || owner_record.members() != object.structured.members
        || !matches!(owner_record.declarations(), Some([declaration])
            if store.source_node_kind(*declaration) == Some(SyntaxKind::TypeLiteral))
    {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    }

    let alias_record = store
        .type_alias(alias)
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    let alias_symbol = alias_record
        .symbol()
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    let alias_symbol_record = store
        .symbol(alias_symbol)
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    if alias_record.type_arguments().is_some()
        || store.get_merged_symbol(alias_symbol) != Some(alias_symbol)
        || alias_symbol_record.flags() != SymbolFlags::TYPE_ALIAS
        || alias_symbol_record.check_flags() != CheckFlags::NONE
        || alias_symbol_record.value_declaration().is_some()
        || alias_symbol_record.exports().is_some()
        || alias_symbol_record.export_symbol().is_some()
        || !matches!(alias_symbol_record.declarations(), Some([declaration])
        if valid_display_type_alias_owner(
            store,
            host,
            alias_symbol,
            alias_symbol_record,
            *declaration,
        ))
        || store.type_alias_links(alias_symbol).is_none_or(|links| {
            links.declared_type != Some(type_id)
                || links.type_parameters.is_some()
                || links.instantiations.is_some()
                || links.is_constructor_declared_property
        })
    {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    }
    Ok(())
}

fn valid_display_type_alias_owner(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    alias_symbol: SemanticSymbolId,
    alias_record: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
) -> bool {
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
        return false;
    }
    match (
        store.source_node_is_exported(declaration),
        alias_record.parent(),
    ) {
        (Some(false), None) => true,
        (Some(true), Some(parent)) => host.is_some_and(|host| {
            let Some(declaration_record) = host.node(declaration) else {
                return false;
            };
            let NodeData::TypeAliasDeclaration(type_alias) = &declaration_record.data else {
                return false;
            };
            if declaration_record.flags.0 != 0
                || type_alias.flow_node.is_some()
                || type_alias.local_symbol.is_some()
                || type_alias.symbol.is_some()
                || type_alias.type_parameters.is_some()
            {
                return false;
            }
            let name = NodeRef::new(declaration.arena, declaration.file, type_alias.name);
            object_members::declared_type_declaration_parent(
                store,
                host,
                declaration,
                alias_symbol,
                name,
                type_alias.modifiers.as_ref(),
            ) == Ok(Some(parent))
        }),
        _ => false,
    }
}

fn validate_structural_object_shell(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    record: &TypeRecord,
) -> Result<StructuralObjectProof, TypeDisplayUnavailable> {
    let TypeData::Object(object) = record.data() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let derived = match global_types {
        Some(global_types) => {
            store.validate_derived_object_literal_with_global_types(type_id, global_types)
        }
        None => store.validate_derived_object_literal_for_relation(type_id),
    };
    match derived {
        DerivedObjectLiteralValidation::Valid { owner, .. } if record.symbol() == Some(owner) => {
            return Ok(StructuralObjectProof::ObjectLiteral);
        }
        DerivedObjectLiteralValidation::Valid { .. } | DerivedObjectLiteralValidation::Invalid => {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        DerivedObjectLiteralValidation::NotDerived => {}
    }
    let allowed_flags = ObjectFlags::ANONYMOUS
        | ObjectFlags::OBJECT_LITERAL
        | ObjectFlags::FRESH_LITERAL
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::FROM_TYPE_NODE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if !(record.object_flags() & !allowed_flags).is_empty()
        || !record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        || record.object_flags().intersects(ObjectFlags::FRESH_LITERAL)
            && !record
                .object_flags()
                .intersects(ObjectFlags::OBJECT_LITERAL)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object
            .structured
            .constrained
            .resolved_base_constraint
            .is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
    }
    if object.structured.call_signature_count != 0
        || object
            .structured
            .signatures
            .as_ref()
            .is_some_and(|signatures| !signatures.is_empty())
        || object
            .structured
            .index_infos
            .as_ref()
            .is_some_and(|index_infos| !index_infos.is_empty())
    {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
    }

    if record
        .object_flags()
        .intersects(ObjectFlags::OBJECT_LITERAL)
    {
        let owner = record
            .symbol()
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        validate_object_literal_contract(store, host, type_id, record, owner)?;
        return Ok(StructuralObjectProof::ObjectLiteral);
    }
    let Some(owner) = record.symbol() else {
        if record
            .object_flags()
            .intersects(ObjectFlags::FROM_TYPE_NODE)
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        return Ok(StructuralObjectProof::Synthetic);
    };
    if host.is_none() {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
    }
    validate_structural_owner(
        store,
        host,
        type_id,
        owner,
        SymbolFlags::TYPE_LITERAL,
        InternalSymbolName::Type,
        object.structured.members,
    )?;
    Ok(StructuralObjectProof::DeclaredTypeLiteral(owner))
}

fn validate_object_literal_contract(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    record: &TypeRecord,
    owner: SemanticSymbolId,
) -> Result<(), TypeDisplayUnavailable> {
    let TypeData::Object(object) = record.data() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let owner_record = store
        .symbol(owner)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    if store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name() != InternalSymbolName::Object.as_ref()
        || owner_record.value_declaration() != Some(*owner_declaration)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.source_node_kind(*owner_declaration) != Some(SyntaxKind::ObjectLiteralExpression)
        || host.is_some_and(|host| {
            host.node(*owner_declaration).is_none()
                || !host.symbol_matches(store, *owner_declaration, owner)
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }

    let result_members = object
        .structured
        .members
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if owner_record.members() == Some(result_members) {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let result_table = store
        .symbol_table(result_members)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let properties = object.structured.properties.as_deref().unwrap_or_default();
    if object.structured.properties.is_some() != !properties.is_empty()
        || result_table.len() != properties.len()
        || owner_record.members().is_some() != !properties.is_empty()
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let raw_table = match owner_record.members() {
        Some(raw_members) => Some(
            store
                .symbol_table(raw_members)
                .filter(|table| table.len() == properties.len())
                .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?,
        ),
        None => None,
    };

    let mut expected_object_flags = ObjectFlags::ANONYMOUS
        | ObjectFlags::OBJECT_LITERAL
        | ObjectFlags::FRESH_LITERAL
        | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
        | ObjectFlags::MEMBERS_RESOLVED;
    let mut raw_targets = HashSet::with_capacity(properties.len());
    for clone in properties {
        let clone_record = store
            .symbol(*clone)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let clone_links = store
            .value_symbol_links(*clone)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let property_type = clone_links
            .resolved_type
            .and_then(|property_type| {
                store
                    .type_payload(property_type)
                    .map(|record| (property_type, record))
            })
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let raw = clone_links
            .target
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let raw_record = store
            .symbol(raw)
            .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let expected_links = ValueSymbolLinks {
            resolved_type: Some(property_type.0),
            target: Some(raw),
            ..ValueSymbolLinks::default()
        };
        if clone_links != &expected_links
            || clone_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
            || clone_record.check_flags() != CheckFlags::NONE
            || clone_record.parent() != Some(owner)
            || clone_record.members().is_some()
            || clone_record.exports().is_some()
            || clone_record.export_symbol().is_some()
            || store.get_merged_symbol(*clone) != Some(*clone)
            || raw_record.flags() != SymbolFlags::PROPERTY
            || raw_record.check_flags() != CheckFlags::NONE
            || raw_record.name() != clone_record.name()
            || raw_record.declarations() != clone_record.declarations()
            || raw_record.value_declaration() != clone_record.value_declaration()
            || raw_record.parent() != Some(owner)
            || raw_record.members().is_some()
            || raw_record.exports().is_some()
            || raw_record.export_symbol().is_some()
            || store.get_merged_symbol(raw) != Some(raw)
            || store
                .value_symbol_links(raw)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
            || !raw_targets.insert(raw)
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        let [declaration] = clone_record.declarations().unwrap_or_default() else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        if clone_record.value_declaration() != Some(*declaration)
            || store.source_node_kind(*declaration) != Some(SyntaxKind::PropertyAssignment)
            || result_table.get(clone_record.name()) != Some(*clone)
            || raw_table.and_then(|table| table.get(raw_record.name())) != Some(raw)
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        expected_object_flags |= property_type.1.object_flags() & ObjectFlags::PROPAGATING_FLAGS;
    }
    if record.object_flags() != expected_object_flags
        || raw_table.is_some_and(|table| table.iter().any(|(_, raw)| !raw_targets.contains(&raw)))
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

fn validate_structural_owner(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    owner: SemanticSymbolId,
    expected_flags: SymbolFlags,
    expected_name: InternalSymbolName,
    members: Option<ts_binder::SymbolTableId>,
) -> Result<(), TypeDisplayUnavailable> {
    let record = store
        .symbol(owner)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if store.get_merged_symbol(owner) != Some(owner)
        || record.flags() != expected_flags
        || record.check_flags() != CheckFlags::NONE
        || record.name() != expected_name.as_ref()
        || record.parent().is_some()
        || record.members() != members
        || record.exports().is_some()
        || record.export_symbol().is_some()
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let declarations = record
        .declarations()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [declaration] = declarations else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let expected_kind = if expected_flags == SymbolFlags::OBJECT_LITERAL {
        SyntaxKind::ObjectLiteralExpression
    } else {
        SyntaxKind::TypeLiteral
    };
    if store.source_node_kind(*declaration) != Some(expected_kind)
        || expected_flags == SymbolFlags::OBJECT_LITERAL
            && record.value_declaration() != Some(*declaration)
        || expected_flags == SymbolFlags::TYPE_LITERAL && record.value_declaration().is_some()
        || host.is_some_and(|host| {
            host.node(*declaration).is_none() || !host.symbol_matches(store, *declaration, owner)
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn display_structural_properties(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    record: &TypeRecord,
    proof: StructuralObjectProof,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let structured = record
        .data()
        .structured()
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    validate_structured_member_table(store, type_id, structured.members, properties)?;
    validate_host_member_order(store, host, type_id, proof, properties)?;
    let properties = properties
        .iter()
        .map(|property| validated_property(store, host, type_id, proof, *property))
        .collect::<Result<Vec<_>, _>>()?;
    if properties.is_empty() {
        state.add(2);
        return Ok("{}".to_owned());
    }
    if state.check_truncation(flags) {
        state.add(2);
        return if flags.contains(CanonicalTypeFormatFlags::NO_TRUNCATION) {
            Ok("{ /*elided*/ }".to_owned())
        } else {
            Ok("{ ...; }".to_owned())
        };
    }

    let mut result = String::from("{ ");
    for (index, property) in properties.iter().copied().enumerate() {
        let display_index = index + 1;
        if state.check_truncation(flags) && display_index + 2 < properties.len() - 1 {
            let elided = properties.len() - display_index;
            if flags.contains(CanonicalTypeFormatFlags::NO_TRUNCATION) {
                write!(result, "/*... {elided} more elided ...*/ ")
                    .expect("writing to a String cannot fail");
            } else {
                write!(result, "... {elided} more ...; ").expect("writing to a String cannot fail");
            }
            append_structural_property(
                store,
                host,
                global_types,
                *properties
                    .last()
                    .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?,
                flags,
                state,
                visiting,
                &mut result,
            )?;
            break;
        }
        append_structural_property(
            store,
            host,
            global_types,
            property,
            flags,
            state,
            visiting,
            &mut result,
        )?;
    }
    result.push('}');
    state.add(2);
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn append_structural_property(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    property: (&str, TypeId, bool, bool),
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
    result: &mut String,
) -> Result<(), TypeDisplayUnavailable> {
    let (name, property_type, optional, readonly) = property;
    if readonly {
        result.push_str("readonly ");
    }
    result.push_str(name);
    state.add(name.len().saturating_add(1));
    if optional {
        result.push('?');
    }
    result.push_str(": ");
    result.push_str(&display_type_worker(
        store,
        host,
        global_types,
        property_type,
        flags,
        state,
        visiting,
    )?);
    if readonly {
        state.add(9);
    }
    result.push_str("; ");
    Ok(())
}

fn validate_structured_member_table(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    members: Option<ts_binder::SymbolTableId>,
    properties: &[SemanticSymbolId],
) -> Result<(), TypeDisplayUnavailable> {
    let property_set = properties.iter().copied().collect::<HashSet<_>>();
    if property_set.len() != properties.len() {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let Some(members) = members else {
        return if properties.is_empty() {
            Ok(())
        } else {
            Err(TypeDisplayUnavailable::MalformedType(type_id))
        };
    };
    let table = store
        .symbol_table(members)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    if table.len() != properties.len()
        || table.iter().any(|(name, property)| {
            !property_set.contains(&property)
                || store
                    .symbol(property)
                    .is_none_or(|symbol| symbol.name() != name)
        })
        || properties.iter().any(|property| {
            store
                .symbol(*property)
                .is_none_or(|symbol| table.get(symbol.name()) != Some(*property))
        })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

fn validate_host_member_order(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    proof: StructuralObjectProof,
    properties: &[SemanticSymbolId],
) -> Result<(), TypeDisplayUnavailable> {
    let StructuralObjectProof::DeclaredTypeLiteral(owner) = proof else {
        return Ok(());
    };
    let host = host.ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    let owner_node = host
        .node(*owner_declaration)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let NodeData::TypeLiteralNode(type_literal) = &owner_node.data else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    if type_literal.members.nodes.len() != properties.len()
        || properties
            .iter()
            .zip(&type_literal.members.nodes)
            .any(|(property, member)| {
                store.symbol(*property).is_none_or(|record| {
                    record.declarations().is_none_or(|declarations| {
                        declarations.len() != 1 || declarations[0].node != *member
                    })
                })
            })
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(())
}

fn validated_property<'a>(
    store: &'a CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    type_id: TypeId,
    proof: StructuralObjectProof,
    property: SemanticSymbolId,
) -> Result<(&'a str, TypeId, bool, bool), TypeDisplayUnavailable> {
    let record = store
        .symbol(property)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let valid_flags_and_checks = match proof {
        StructuralObjectProof::Synthetic => {
            let allowed = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT;
            record.flags().contains(SymbolFlags::PROPERTY)
                && record.flags().without(allowed) == SymbolFlags::NONE
                && record.check_flags().bits() & !CheckFlags::READONLY.bits() == 0
        }
        StructuralObjectProof::ObjectLiteral => {
            record.flags() == (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
                && record.check_flags() == CheckFlags::NONE
        }
        StructuralObjectProof::DeclaredTypeLiteral(_) => {
            let allowed = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
            record.flags().contains(SymbolFlags::PROPERTY)
                && record.flags().without(allowed) == SymbolFlags::NONE
                && record.check_flags().bits() & !CheckFlags::READONLY.bits() == 0
        }
    };
    if !valid_flags_and_checks
        || record.name().is_reserved_member_name()
        || record.name().is_private_identifier()
        || record.name().is_late_bound()
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(property) != Some(property)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let name = record
        .name()
        .as_utf8()
        .filter(|name| is_plain_identifier(name))
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let optional = record.flags().intersects(SymbolFlags::OPTIONAL);
    let links = store
        .value_symbol_links(property)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let property_type = links
        .resolved_type
        .filter(|property_type| store.type_payload(*property_type).is_some())
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let expected_links = match proof {
        StructuralObjectProof::ObjectLiteral => ValueSymbolLinks {
            resolved_type: Some(property_type),
            target: links.target,
            ..ValueSymbolLinks::default()
        },
        StructuralObjectProof::Synthetic | StructuralObjectProof::DeclaredTypeLiteral(_) => {
            ValueSymbolLinks {
                resolved_type: Some(property_type),
                ..ValueSymbolLinks::default()
            }
        }
    };
    if links != &expected_links
        || matches!(proof, StructuralObjectProof::ObjectLiteral) && links.target.is_none()
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }

    let readonly = match proof {
        StructuralObjectProof::Synthetic => {
            if record.parent().is_some()
                || record
                    .declarations()
                    .is_some_and(|declarations| !declarations.is_empty())
                || record.value_declaration().is_some()
            {
                return Err(TypeDisplayUnavailable::MalformedType(type_id));
            }
            record.check_flags().contains(CheckFlags::READONLY)
        }
        StructuralObjectProof::ObjectLiteral => false,
        StructuralObjectProof::DeclaredTypeLiteral(owner) => {
            let host = host.ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
            validate_declared_property(
                store, host, type_id, owner, property, record, name, optional,
            )?
        }
    };
    Ok((name, property_type, optional, readonly))
}

#[allow(clippy::too_many_arguments)]
fn validate_declared_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_id: TypeId,
    owner: SemanticSymbolId,
    property: SemanticSymbolId,
    record: &ts_binder::semantic::Symbol,
    name: &str,
    optional: bool,
) -> Result<bool, TypeDisplayUnavailable> {
    let [declaration] = record.declarations().unwrap_or_default() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    if record.parent() != Some(owner)
        || record.value_declaration() != Some(*declaration)
        || store.get_merged_symbol(property) != Some(property)
        || !host.symbol_matches(store, *declaration, property)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let node = host
        .node(*declaration)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let (name_node, postfix_token, modifiers) = match &node.data {
        NodeData::PropertyDeclaration(property) => (
            property.name,
            property.postfix_token,
            property.modifiers.as_ref(),
        ),
        NodeData::PropertySignatureDeclaration(property) => (
            property.name,
            property.postfix_token,
            property.modifiers.as_ref(),
        ),
        _ => return Err(TypeDisplayUnavailable::MalformedType(type_id)),
    };
    let owner_record = store
        .symbol(owner)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    if declaration.arena != owner_declaration.arena
        || declaration.file != owner_declaration.file
        || node.parent != Some(owner_declaration.node)
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    let (arena, _) = host
        .source(*declaration)
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
    let name_matches = arena.get(name_node).is_some_and(
        |name_node| matches!(&name_node.data, NodeData::Identifier(data) if data.text == name),
    );
    let syntax_optional = match postfix_token {
        None => false,
        Some(token)
            if arena
                .get(token)
                .is_some_and(|token| token.kind == SyntaxKind::QuestionToken) =>
        {
            true
        }
        Some(_) => return Err(TypeDisplayUnavailable::MalformedType(type_id)),
    };
    let valid_modifiers = modifiers.is_none_or(|modifiers| {
        modifiers.flags.0 == 0
            && !modifiers.list.has_trailing_comma
            && modifiers.list.nodes.len() == 1
            && arena
                .get(modifiers.list.nodes[0])
                .is_some_and(|modifier| modifier.kind == SyntaxKind::ReadonlyKeyword)
    });
    let readonly =
        canonical_has_syntactic_modifier(arena, declaration.node, SyntaxKind::ReadonlyKeyword);
    let expected_check_flags = if readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    if !name_matches
        || syntax_optional != optional
        || !valid_modifiers
        || record.check_flags() != expected_check_flags
    {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    }
    Ok(readonly)
}

fn display_symbol_name(
    store: &CanonicalTypeMapperStore,
    _type_id: TypeId,
    symbol: SemanticSymbolId,
    state: &mut DisplayState,
) -> Option<String> {
    let symbol = store.symbol(symbol)?;
    let escaped_name = symbol.name();
    if escaped_name.is_reserved_member_name()
        || escaped_name.is_internal()
        || escaped_name.is_private_identifier()
        || escaped_name.is_late_bound()
    {
        return None;
    }
    let name = escaped_name
        .as_utf8()
        .filter(|name| is_plain_identifier(name))?;
    state.add(name.len().saturating_add(1).saturating_mul(2));
    Some(name.to_owned())
}

fn is_plain_identifier(name: &str) -> bool {
    let mut characters = name.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || matches!(first, '_' | '$'))
        && characters
            .all(|character| character.is_ascii_alphanumeric() || matches!(character, '_' | '$'))
}

#[allow(clippy::too_many_arguments)]
fn display_intersection_type(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let projection = store
        .validate_intersection_type(type_id)
        .map_err(|_| TypeDisplayUnavailable::InvalidIntersection(type_id))?;
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    let result = (|| {
        let record = store
            .type_payload(type_id)
            .ok_or(TypeDisplayUnavailable::Type(type_id))?;
        if let Some(alias) = record.alias() {
            return display_alias_name(store, type_id, alias, state);
        }
        let mut result = String::new();
        for (index, constituent) in projection.types.iter().enumerate() {
            if index != 0 {
                state.add(3);
                result.push_str(" & ");
            }
            result.push_str(&display_type_worker(
                store,
                host,
                global_types,
                *constituent,
                flags,
                state,
                visiting,
            )?);
        }
        Ok(result)
    })();
    visiting.remove(&type_id);
    result
}

fn display_union_type(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    ensure_acyclic_union_graph(store, type_id)?;
    validate_display_union(store, global_types, type_id)?;
    if !visiting.insert(type_id) {
        return Err(TypeDisplayUnavailable::CyclicType(type_id));
    }
    let result = (|| {
        let record = store
            .type_payload(type_id)
            .ok_or(TypeDisplayUnavailable::Type(type_id))?;
        if let Some(alias) = record.alias() {
            return display_alias_name(store, type_id, alias, state);
        }
        let TypeData::Union(data) = record.data() else {
            return Err(TypeDisplayUnavailable::InvalidUnion(type_id));
        };
        let display_union = data.origin.unwrap_or(type_id);
        let display_record = store
            .type_payload(display_union)
            .ok_or(TypeDisplayUnavailable::Type(display_union))?;
        match display_record.data() {
            TypeData::Union(display_data) => {
                let types = format_union_types(store, type_id, &display_data.union.types)?;
                display_union_list(
                    store,
                    host,
                    global_types,
                    type_id,
                    &types,
                    flags,
                    state,
                    visiting,
                )
            }
            TypeData::Index(_) => display_type_worker(
                store,
                host,
                global_types,
                display_union,
                flags,
                state,
                visiting,
            ),
            _ => Err(TypeDisplayUnavailable::InvalidUnion(type_id)),
        }
    })();
    visiting.remove(&type_id);
    result
}

fn display_alias_name(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    alias: TypeAliasId,
    state: &mut DisplayState,
) -> Result<String, TypeDisplayUnavailable> {
    let alias_record = store
        .type_alias(alias)
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    let symbol = alias_record
        .symbol()
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })?;
    display_symbol_name(store, type_id, symbol, state)
        .ok_or(TypeDisplayUnavailable::Alias { type_id, alias })
}

fn format_union_types(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    types: &[TypeId],
) -> Result<Vec<TypeId>, TypeDisplayUnavailable> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(TypeDisplayUnavailable::MissingBootstrap)?;
    let boolean_types = union_payload_types(store, bootstrap.boolean_type)?;
    let boolean_last = boolean_types
        .last()
        .copied()
        .ok_or(TypeDisplayUnavailable::InvalidUnion(bootstrap.boolean_type))?;
    let boolean_last = regular_literal_type(store, boolean_last)?;

    let mut result = Vec::with_capacity(types.len());
    let mut combined_flags = TypeFlags::NONE;
    let mut index = 0;
    while index < types.len() {
        let type_id = types[index];
        let record = store.type_payload(type_id).ok_or(
            TypeDisplayUnavailable::UnsupportedUnionConstituent {
                union,
                constituent: type_id,
            },
        )?;
        combined_flags |= record.flags();
        if !record.flags().intersects(TypeFlags::NULLABLE) {
            if record.flags().intersects(TypeFlags::BOOLEAN_LITERAL) {
                let count = boolean_types.len();
                if index + count <= types.len()
                    && regular_literal_type(store, types[index + count - 1])? == boolean_last
                {
                    result.push(bootstrap.boolean_type);
                    index += count;
                    continue;
                }
            }
            result.push(type_id);
        }
        index += 1;
    }
    if combined_flags.intersects(TypeFlags::NULL) {
        result.push(bootstrap.null_type);
    }
    if combined_flags.intersects(TypeFlags::UNDEFINED) {
        result.push(bootstrap.undefined_type);
    }
    if result.is_empty() {
        return Err(TypeDisplayUnavailable::InvalidUnion(union));
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)] // Keeps recursive display capabilities explicit.
fn display_union_list(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    union: TypeId,
    types: &[TypeId],
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    if types.len() == 1 {
        return display_type_worker(store, host, global_types, types[0], flags, state, visiting);
    }
    if state.check_truncation(flags) && types.len() > 2 {
        let first =
            display_union_constituent(store, host, global_types, types[0], flags, state, visiting)?;
        let last = display_union_constituent(
            store,
            host,
            global_types,
            *types
                .last()
                .ok_or(TypeDisplayUnavailable::InvalidUnion(union))?,
            flags,
            state,
            visiting,
        )?;
        return Ok(format!(
            "{first} | {} | {last}",
            union_elision(types.len() - 2, flags)
        ));
    }

    let mut displayed = Vec::with_capacity(types.len());
    for (index, type_id) in types.iter().copied().enumerate() {
        let display_index = index + 1;
        if state.check_truncation(flags) && display_index + 2 < types.len() - 1 {
            displayed.push(union_elision(types.len() - display_index, flags));
            displayed.push(display_union_constituent(
                store,
                host,
                global_types,
                *types
                    .last()
                    .ok_or(TypeDisplayUnavailable::InvalidUnion(union))?,
                flags,
                state,
                visiting,
            )?);
            break;
        }
        state.add(2);
        displayed.push(display_union_constituent(
            store,
            host,
            global_types,
            type_id,
            flags,
            state,
            visiting,
        )?);
    }
    Ok(displayed.join(" | "))
}

#[allow(clippy::too_many_arguments)]
fn display_union_constituent(
    store: &CanonicalTypeMapperStore,
    host: Option<&DeclaredTypeHost<'_>>,
    global_types: Option<&CanonicalGlobalTypes>,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
    state: &mut DisplayState,
    visiting: &mut HashSet<TypeId>,
) -> Result<String, TypeDisplayUnavailable> {
    let displayed =
        display_type_worker(store, host, global_types, type_id, flags, state, visiting)?;
    Ok(if is_unaliased_single_callable_type(store, type_id) {
        format!("({displayed})")
    } else {
        displayed
    })
}

fn is_unaliased_single_callable_type(store: &CanonicalTypeMapperStore, type_id: TypeId) -> bool {
    single_callable_family(store, type_id).is_some()
        && store
            .type_payload(type_id)
            .is_some_and(|record| record.alias().is_none())
}

fn union_elision(count: usize, flags: CanonicalTypeFormatFlags) -> String {
    if flags.contains(CanonicalTypeFormatFlags::NO_TRUNCATION) {
        format!("/*... {count} more elided ...*/ any")
    } else {
        format!("... {count} more ...")
    }
}

fn union_payload_types(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<&[TypeId], TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_id)
        .ok_or(TypeDisplayUnavailable::Type(type_id))?;
    let TypeData::Union(data) = record.data() else {
        return Err(TypeDisplayUnavailable::InvalidUnion(type_id));
    };
    Ok(&data.union.types)
}

fn regular_literal_type(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<TypeId, TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_id)
        .ok_or(TypeDisplayUnavailable::Type(type_id))?;
    Ok(match record.data() {
        TypeData::Literal(literal) if record.flags().intersects(TypeFlags::FRESHABLE) => {
            literal.regular_type
        }
        _ => type_id,
    })
}

fn ensure_acyclic_union_graph(
    store: &CanonicalTypeMapperStore,
    root: TypeId,
) -> Result<(), TypeDisplayUnavailable> {
    fn visit(
        store: &CanonicalTypeMapperStore,
        type_id: TypeId,
        visiting: &mut HashSet<TypeId>,
        visited: &mut HashSet<TypeId>,
    ) -> Result<(), TypeDisplayUnavailable> {
        if visited.contains(&type_id) {
            return Ok(());
        }
        let record = store
            .type_payload(type_id)
            .ok_or(TypeDisplayUnavailable::Type(type_id))?;
        let TypeData::Union(data) = record.data() else {
            return Ok(());
        };
        if !visiting.insert(type_id) {
            return Err(TypeDisplayUnavailable::CyclicType(type_id));
        }
        for constituent in &data.union.types {
            visit(store, *constituent, visiting, visited)?;
        }
        if let Some(origin) = data.origin {
            visit(store, origin, visiting, visited)?;
        }
        visiting.remove(&type_id);
        visited.insert(type_id);
        Ok(())
    }

    visit(store, root, &mut HashSet::new(), &mut HashSet::new())
}

fn validate_display_union(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    union: TypeId,
) -> Result<(), TypeDisplayUnavailable> {
    let result = match global_types {
        Some(global_types) => {
            store.validate_union_constituent_with_global_types(global_types, union)
        }
        None => store.validate_union_constituent(union),
    };
    result.map_err(|error| union_display_unavailable(union, error))
}

const fn union_display_unavailable(
    union: TypeId,
    error: LiteralTypeCacheError,
) -> TypeDisplayUnavailable {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => TypeDisplayUnavailable::MissingBootstrap,
        LiteralTypeCacheError::InvalidCachedLiteral(type_id) => {
            TypeDisplayUnavailable::InvalidLiteralLinks(type_id)
        }
        LiteralTypeCacheError::UnsupportedUnionConstituent(constituent) => {
            TypeDisplayUnavailable::UnsupportedUnionConstituent { union, constituent }
        }
        LiteralTypeCacheError::ArrayType { error, .. } => TypeDisplayUnavailable::ArrayType(error),
        LiteralTypeCacheError::InvalidValue
        | LiteralTypeCacheError::InvalidCachedUnion(_)
        | LiteralTypeCacheError::InvalidUnionAlias(_)
        | LiteralTypeCacheError::InvalidPreparedQuery
        | LiteralTypeCacheError::Capacity => TypeDisplayUnavailable::InvalidUnion(union),
    }
}

fn require_data_kind(
    type_id: TypeId,
    record: &TypeRecord,
    expected: TypeDataKind,
) -> Result<(), TypeDisplayUnavailable> {
    if record.data().kind() == expected {
        Ok(())
    } else {
        Err(TypeDisplayUnavailable::MalformedType(type_id))
    }
}

fn literal_data(
    type_id: TypeId,
    record: &TypeRecord,
) -> Result<&LiteralTypeData, TypeDisplayUnavailable> {
    let TypeData::Literal(literal) = record.data() else {
        return Err(TypeDisplayUnavailable::MalformedType(type_id));
    };
    Ok(literal)
}

fn validate_literal_links(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    record: &TypeRecord,
    literal: &LiteralTypeData,
) -> Result<(), TypeDisplayUnavailable> {
    let regular = literal.regular_type;
    let Some(regular_record) = store.type_payload(regular) else {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    };
    let TypeData::Literal(regular_literal) = regular_record.data() else {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    };
    if regular_record.flags() != record.flags()
        || !literal_values_equal(&regular_literal.value, &literal.value)
        || regular_literal.regular_type != regular
    {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    }

    if type_id != regular {
        if literal.fresh_type != Some(type_id) || regular_literal.fresh_type != Some(type_id) {
            return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
        }
        return Ok(());
    }

    let Some(fresh) = regular_literal.fresh_type else {
        return Ok(());
    };
    if fresh == regular {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    }
    let Some(fresh_record) = store.type_payload(fresh) else {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    };
    let TypeData::Literal(fresh_literal) = fresh_record.data() else {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    };
    if fresh_record.flags() != record.flags()
        || !literal_values_equal(&fresh_literal.value, &literal.value)
        || fresh_literal.regular_type != regular
        || fresh_literal.fresh_type != Some(fresh)
    {
        return Err(TypeDisplayUnavailable::InvalidLiteralLinks(type_id));
    }
    Ok(())
}

fn literal_values_equal(left: &LiteralValue, right: &LiteralValue) -> bool {
    match (left, right) {
        (LiteralValue::String(left), LiteralValue::String(right)) => left == right,
        (LiteralValue::Number(left), LiteralValue::Number(right)) => {
            left == right || left.is_nan() && right.is_nan()
        }
        (LiteralValue::Boolean(left), LiteralValue::Boolean(right)) => left == right,
        (LiteralValue::BigInt(left), LiteralValue::BigInt(right)) => left == right,
        (LiteralValue::ComputedEnum, LiteralValue::ComputedEnum) => true,
        _ => false,
    }
}

fn is_literal_type(record: &TypeRecord) -> bool {
    record
        .flags()
        .intersects(TypeFlags::BOOLEAN | TypeFlags::UNIT)
}

fn type_could_have_top_level_singleton_types(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(TypeDisplayUnavailable::Type(type_))?;
    // Pinned behavior intentionally treats `boolean` as non-singleton even
    // though its representation is `false | true`.
    if record.flags().intersects(TypeFlags::BOOLEAN) {
        return Ok(false);
    }
    if record.flags().intersects(TypeFlags::UNION_OR_INTERSECTION) {
        if !visiting.insert(type_) {
            return Err(TypeDisplayUnavailable::CyclicType(type_));
        }
        let result = (|| {
            let constituents = match record.data() {
                TypeData::Union(union) => &union.union.types,
                TypeData::Intersection(intersection) => &intersection.intersection.types,
                _ => return Err(TypeDisplayUnavailable::MalformedType(type_)),
            };
            for constituent in constituents {
                if type_could_have_top_level_singleton_types(store, *constituent, visiting)? {
                    return Ok(true);
                }
            }
            Ok(false)
        })();
        assert!(visiting.remove(&type_));
        return result;
    }
    Ok(record.flags().intersects(TypeFlags::UNIT))
}

fn base_type_of_literal_type(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    record: &TypeRecord,
) -> Result<TypeId, TypeDisplayUnavailable> {
    let flags = record.flags();
    if flags.intersects(TypeFlags::STRING_LITERAL) {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.string_type)
            .ok_or(TypeDisplayUnavailable::MissingBootstrap);
    }
    if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.number_type)
            .ok_or(TypeDisplayUnavailable::MissingBootstrap);
    }
    if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.bigint_type)
            .ok_or(TypeDisplayUnavailable::MissingBootstrap);
    }
    if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.boolean_type)
            .ok_or(TypeDisplayUnavailable::MissingBootstrap);
    }
    Ok(source)
}

fn quote_string_literal(value: &str, quote: char) -> String {
    let mut result = String::with_capacity(value.len() + 2);
    result.push(quote);
    let mut characters = value.chars().peekable();
    while let Some(character) = characters.next() {
        let next_is_digit = characters.peek().is_some_and(char::is_ascii_digit);
        let needs_escape = character == '\\'
            || character == quote
            || character <= '\u{001f}'
            || matches!(character, '\u{0085}' | '\u{2028}' | '\u{2029}');
        if !needs_escape {
            result.push(character);
            continue;
        }
        match character {
            '\0' if next_is_digit => result.push_str("\\x00"),
            '\0' => result.push_str("\\0"),
            '\t' => result.push_str("\\t"),
            '\u{000b}' => result.push_str("\\v"),
            '\u{000c}' => result.push_str("\\f"),
            '\u{0008}' => result.push_str("\\b"),
            '\r' => result.push_str("\\r"),
            '\n' => result.push_str("\\n"),
            '\\' => result.push_str("\\\\"),
            character if character == quote => {
                result.push('\\');
                result.push(character);
            }
            character => {
                write!(result, "\\u{:04X}", u32::from(character))
                    .expect("writing to a String cannot fail");
            }
        }
    }
    result.push(quote);
    result
}

fn truncate_display(
    type_id: TypeId,
    display: String,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    let maximum = if flags.contains(CanonicalTypeFormatFlags::NO_TRUNCATION) {
        NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH * 2
    } else {
        DEFAULT_MAXIMUM_TRUNCATION_LENGTH * 2
    };
    if display.is_empty() || display.len() < maximum {
        return Ok(display);
    }
    let boundary = maximum - ELLIPSIS.len();
    if !display.is_char_boundary(boundary) {
        return Err(TypeDisplayUnavailable::Utf8TruncationBoundary { type_id, boundary });
    }
    let mut truncated = display[..boundary].to_owned();
    truncated.push_str(ELLIPSIS);
    Ok(truncated)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SymbolData, SymbolFlags,
    };
    use ts_diagnostics::{Diagnostic, message_by_code};
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
        bootstrap::UnionReduction,
        type_records::{ConstituentMapState, LiteralValue, RegularLiteralLink},
        types::ObjectFlags,
    };

    fn bootstrapped_store() -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::default();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn strict_bootstrapped_store() -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::default();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn canonical_union(store: &mut CanonicalTypeMapperStore, types: &[TypeId]) -> TypeId {
        store.literal_union_type(types, None).unwrap()
    }

    fn named_canonical_union(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        types: &[TypeId],
    ) -> TypeId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source(name),
            ))
            .unwrap();
        store.literal_union_type(types, Some(symbol)).unwrap()
    }

    fn fresh_literal(store: &CanonicalTypeMapperStore, regular: TypeId) -> TypeId {
        let TypeData::Literal(literal) = store.type_payload(regular).unwrap().data() else {
            panic!("expected literal")
        };
        literal.fresh_type.expect("regular literal has fresh pair")
    }

    fn attach_type_alias(
        store: &mut CanonicalTypeMapperStore,
        type_id: TypeId,
        name: &str,
    ) -> TypeAliasId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source(name),
            ))
            .unwrap();
        let alias = store.alloc_type_alias(Some(symbol)).unwrap();
        assert!(store.set_type_alias(type_id, Some(alias)));
        alias
    }

    fn alloc_typed_property(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_id: TypeId,
        optional: bool,
        readonly: bool,
    ) -> SemanticSymbolId {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let property = if readonly {
            store.alloc_transient_symbol(flags, EscapedName::source(name), CheckFlags::READONLY)
        } else {
            store
                .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
                .unwrap()
        };
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(type_id),
                ..ValueSymbolLinks::default()
            },
        ));
        property
    }

    fn set_object_properties(
        store: &mut CanonicalTypeMapperStore,
        object: TypeId,
        properties: Vec<SemanticSymbolId>,
    ) {
        let members = if properties.is_empty() {
            None
        } else {
            let members = store.alloc_symbol_table();
            for property in &properties {
                let name = store
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned();
                assert_eq!(
                    store.insert_symbol(members, EscapedName::source(&name), *property),
                    Some(None),
                );
            }
            Some(members)
        };
        let properties = (!properties.is_empty()).then_some(properties);
        assert!(store.set_structured_type_members(object, members, properties, None, None, None,));
    }

    fn alloc_structural_object(
        store: &mut CanonicalTypeMapperStore,
        properties: Vec<SemanticSymbolId>,
    ) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        set_object_properties(store, object, properties);
        object
    }

    fn alloc_named_interface(store: &mut CanonicalTypeMapperStore, name: &str) -> TypeId {
        let parsed = parse_source_file(&format!("interface {name} {{}}"));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(191);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut symbol_data = SymbolData::new(SymbolFlags::INTERFACE, EscapedName::source(name));
        symbol_data.declarations = Some(vec![declaration]);
        let symbol = store.alloc_symbol(symbol_data).unwrap();
        let interface = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        assert!(store.set_declared_type_links(
            symbol,
            crate::semantic::DeclaredTypeLinks {
                declared_type: Some(interface),
                ..crate::semantic::DeclaredTypeLinks::default()
            },
        ));
        interface
    }

    fn alloc_named_object_alias(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
    ) -> (TypeId, TypeAliasId) {
        let parsed = parse_source_file(&format!("type {name} = {{}};"));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(194);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let alias_declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let type_literal = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut owner_data = SymbolData::new(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
        );
        owner_data.declarations = Some(vec![type_literal]);
        let owner = store.alloc_symbol(owner_data).unwrap();
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        let mut alias_data = SymbolData::new(SymbolFlags::TYPE_ALIAS, EscapedName::source(name));
        alias_data.declarations = Some(vec![alias_declaration]);
        let alias_symbol = store.alloc_symbol(alias_data).unwrap();
        let alias = store.alloc_type_alias(Some(alias_symbol)).unwrap();
        assert!(store.set_type_alias(object, Some(alias)));
        assert!(store.set_type_alias_links(
            alias_symbol,
            crate::semantic::TypeAliasLinks {
                declared_type: Some(object),
                ..crate::semantic::TypeAliasLinks::default()
            },
        ));
        (object, alias)
    }

    fn parsed_context(
        parsed: &ParseResult,
        file: FileId,
        options: impl Into<CanonicalCheckerOptions>,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/formatter.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
    }

    fn external_parsed_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/formatter-external.ts\""),
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
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn type_alias_body(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == expected).then(|| NodeRef::new(parsed.arena.id(), file, alias.type_))
            })
            .expect("the test source contains the requested type alias")
    }

    fn type_literal_member(
        parsed: &ParseResult,
        file: FileId,
        alias: &str,
        kind: SyntaxKind,
    ) -> (NodeRef, NodeRef) {
        let literal = type_alias_body(parsed, file, alias);
        let NodeData::TypeLiteralNode(data) = &parsed.arena.get(literal.node).unwrap().data else {
            panic!("the requested alias does not contain a type literal")
        };
        let member = data
            .members
            .nodes
            .iter()
            .copied()
            .find(|member| {
                parsed
                    .arena
                    .get(*member)
                    .is_some_and(|member| member.kind == kind)
            })
            .expect("the type literal contains the requested member kind");
        (literal, NodeRef::new(parsed.arena.id(), file, member))
    }

    fn variable_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then(|| {
                    NodeRef::new(
                        parsed.arena.id(),
                        file,
                        variable.type_.expect("test variable has an annotation"),
                    )
                })
            })
            .expect("the test source contains the requested variable")
    }

    fn function_type_nodes(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::FunctionType)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
    }

    fn function_signature(
        context: &CanonicalCheckerContext<'_>,
        function: NodeRef,
    ) -> Option<SignatureId> {
        context
            .store()
            .signature_links(function)
            .and_then(|links| links.resolved_signature.signature())
    }

    fn function_parameter_symbol(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        function: NodeRef,
        index: usize,
    ) -> SemanticSymbolId {
        let parameter = match &parsed.arena.get(function.node).unwrap().data {
            NodeData::FunctionTypeNode(data) => {
                NodeRef::new(function.arena, function.file, data.parameters.nodes[index])
            }
            _ => unreachable!(),
        };
        context
            .file(function.file)
            .unwrap()
            .1
            .symbol(parameter)
            .unwrap()
    }

    fn resolve_all_function_returns(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
    ) {
        let functions = function_type_nodes(parsed, file);
        for _ in 0..=functions.len() {
            let unresolved = functions
                .iter()
                .filter_map(|function| function_signature(context, *function))
                .filter(|signature| {
                    context
                        .store()
                        .signature(*signature)
                        .is_some_and(|signature| signature.resolved_return_type().is_none())
                })
                .collect::<Vec<_>>();
            if unresolved.is_empty() {
                return;
            }
            for signature in unresolved {
                context.get_return_type_of_signature(signature).unwrap();
            }
        }
        panic!("nested function returns did not reach a fixed point");
    }

    #[test]
    fn formats_named_interfaces_object_aliases_and_property_only_structures() {
        let mut store = bootstrapped_store();
        let (string, number) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| (bootstrap.string_type, bootstrap.number_type))
            .unwrap();
        let interface = alloc_named_interface(&mut store, "Shape");
        let (alias, _) = alloc_named_object_alias(&mut store, "AliasShape");
        let nested_value = alloc_typed_property(&mut store, "value", string, false, false);
        let nested = alloc_structural_object(&mut store, vec![nested_value]);
        let first = alloc_typed_property(&mut store, "a", string, false, false);
        let second = alloc_typed_property(&mut store, "b", number, true, false);
        let child = alloc_typed_property(&mut store, "child", nested, false, false);
        let object = alloc_structural_object(&mut store, vec![first, second, child]);
        let empty = alloc_structural_object(&mut store, Vec::new());

        assert_eq!(type_to_string(&store, interface).unwrap(), "Shape");
        assert_eq!(type_to_string(&store, alias).unwrap(), "AliasShape");
        assert_eq!(type_to_string(&store, empty).unwrap(), "{}");
        assert_eq!(
            type_to_string(&store, object).unwrap(),
            "{ a: string; b?: number; child: { value: string; }; }",
        );
    }

    #[test]
    fn direct_generic_references_format_target_names_and_ordered_arguments() {
        let parsed = parse_source_file(concat!(
            "interface Box<T> {} ",
            "class Pair<Left, Right> {} ",
            "type Plain = Box<string>; ",
            "type Nested = Box<Box<string>>; ",
            "type Mixed = Pair<string, number>; ",
            "type UnionArgument = Box<string | number>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(196);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());

        for (alias, expected) in [
            ("Plain", "Box<string>"),
            ("Nested", "Box<Box<string>>"),
            ("Mixed", "Pair<string, number>"),
            ("UnionArgument", "Box<string | number>"),
        ] {
            let node = type_alias_body(&parsed, file, alias);
            let reference = context.get_type_from_type_node(node).unwrap();
            assert_eq!(context.type_to_string(reference).unwrap(), expected);
        }

        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let target = context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        assert_eq!(context.type_to_string(target).unwrap(), "Box<T>");

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().relation_state_snapshot(),
        );
        assert_eq!(context.type_to_string(target).unwrap(), "Box<T>");
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().relation_state_snapshot(),
            ),
            warm
        );
    }

    #[test]
    fn global_aware_array_display_uses_suffix_syntax_and_literal_clone_shape() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = parsed_context(
            &parsed,
            FileId::new(195),
            CanonicalCheckerOptions::default(),
        );
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string) = (bootstrap.number_type, bootstrap.string_type);
        let store = context.store_mut_for_test();

        let number_array = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let number_literal_array = store
            .create_array_literal_type(&global_types, number_array)
            .unwrap();
        let id = alloc_typed_property(store, "id", number, false, false);
        let object = alloc_structural_object(store, vec![id]);
        let object_array = store
            .create_canonical_array_type(&global_types, object, false)
            .unwrap();
        let object_literal_array = store
            .create_array_literal_type(&global_types, object_array)
            .unwrap();
        let primitive_union = canonical_union(store, &[number, string]);
        let union_array = store
            .create_canonical_array_type(&global_types, primitive_union, false)
            .unwrap();
        let named_t = alloc_named_interface(store, "T");
        let readonly_array = store
            .create_canonical_array_type(&global_types, named_t, true)
            .unwrap();
        let nested_array = store
            .create_canonical_array_type(&global_types, number_literal_array, false)
            .unwrap();
        let nested_literal_array = store
            .create_array_literal_type(&global_types, nested_array)
            .unwrap();
        let nested_union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[nested_literal_array, string],
                UnionReduction::None,
            )
            .unwrap();

        assert!(matches!(
            type_to_string(store, number_array),
            Err(TypeDisplayUnavailable::UnsupportedType {
                type_id,
                kind: TypeDataKind::TypeReference,
            }) if type_id == number_array
        ));
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, number_array).unwrap(),
            "number[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, number_literal_array).unwrap(),
            "number[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, object_array).unwrap(),
            "{ id: number; }[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, object_literal_array).unwrap(),
            "{ id: number; }[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, union_array).unwrap(),
            "(string | number)[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, readonly_array).unwrap(),
            "readonly T[]"
        );
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, nested_literal_array).unwrap(),
            "number[][]"
        );
        assert!(matches!(
            type_to_string(store, nested_union),
            Err(TypeDisplayUnavailable::UnsupportedUnionConstituent {
                union,
                constituent,
            }) if union == nested_union && constituent == nested_literal_array
        ));
        assert_eq!(
            type_to_string_with_global_types(store, &global_types, nested_union).unwrap(),
            "string | number[][]"
        );
        assert_eq!(
            get_type_names_for_assignability_error_with_global_types(
                store,
                &global_types,
                object_literal_array,
                number_array,
            )
            .unwrap(),
            AssignabilityErrorDisplay {
                source: "{ id: number; }[]".to_owned(),
                target: "number[]".to_owned(),
            }
        );
    }

    #[test]
    fn prints_readonly_only_from_a_checker_owned_semantic_proof() {
        let mut store = bootstrapped_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let readonly = alloc_typed_property(&mut store, "value", string, false, true);
        let object = alloc_structural_object(&mut store, vec![readonly]);

        assert_eq!(
            type_to_string(&store, object).unwrap(),
            "{ readonly value: string; }",
        );
    }

    #[test]
    fn structural_cycles_and_poisoned_member_caches_fail_typed_without_writes() {
        let mut cyclic_store = bootstrapped_store();
        let cyclic = cyclic_store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let self_property = alloc_typed_property(&mut cyclic_store, "self", cyclic, false, false);
        set_object_properties(&mut cyclic_store, cyclic, vec![self_property]);
        assert_eq!(
            type_to_string(&cyclic_store, cyclic),
            Err(TypeDisplayUnavailable::CyclicType(cyclic)),
        );

        let mut poisoned_store = bootstrapped_store();
        let string = poisoned_store.intrinsic_bootstrap().unwrap().string_type;
        let property = alloc_typed_property(&mut poisoned_store, "value", string, false, false);
        let poisoned = poisoned_store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let members = poisoned_store.alloc_symbol_table();
        assert_eq!(
            poisoned_store.insert_symbol(members, EscapedName::source("value"), property,),
            Some(None),
        );
        assert!(poisoned_store.set_structured_type_members(
            poisoned,
            Some(members),
            Some(vec![property, property]),
            None,
            None,
            None,
        ));
        let before = (
            poisoned_store.type_len(),
            poisoned_store.symbol_len(),
            poisoned_store.type_alias_len(),
            poisoned_store.mapper_len(),
            poisoned_store.relation_state_snapshot(),
        );
        assert_eq!(
            type_to_string(&poisoned_store, poisoned),
            Err(TypeDisplayUnavailable::MalformedType(poisoned)),
        );
        assert_eq!(
            (
                poisoned_store.type_len(),
                poisoned_store.symbol_len(),
                poisoned_store.type_alias_len(),
                poisoned_store.mapper_len(),
                poisoned_store.relation_state_snapshot(),
            ),
            before,
        );
    }

    #[test]
    fn named_object_cache_provenance_is_validated_before_display() {
        let mut alias_store = bootstrapped_store();
        let string = alias_store.intrinsic_bootstrap().unwrap().string_type;
        let (object, alias) = alloc_named_object_alias(&mut alias_store, "Shape");
        assert_eq!(type_to_string(&alias_store, object).unwrap(), "Shape");
        assert!(alias_store.set_type_alias_arguments(alias, Some(vec![string])));
        assert_eq!(
            type_to_string(&alias_store, object),
            Err(TypeDisplayUnavailable::Alias {
                type_id: object,
                alias,
            }),
        );

        let mut interface_store = bootstrapped_store();
        let symbol = interface_store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("Unlinked"),
            ))
            .unwrap();
        let interface = interface_store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        assert_eq!(
            type_to_string(&interface_store, interface),
            Err(TypeDisplayUnavailable::MalformedType(interface)),
        );
    }

    #[test]
    fn exported_alias_display_requires_host_proof_and_rejects_export_table_poison() {
        let parsed = parse_source_file(concat!(
            "export type User = { id: number }; ",
            "export type Other = { id: number };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(194);
        let mut context = external_parsed_context(&parsed, file);
        let (exports, user, other) = {
            let (_, bound) = context.file(file).unwrap();
            let module = bound.symbol(bound.source_file()).unwrap();
            let exports = context.store().symbol(module).unwrap().exports().unwrap();
            let table = context.store().symbol_table(exports).unwrap();
            (
                exports,
                table.get_source("User").unwrap(),
                table.get_source("Other").unwrap(),
            )
        };
        let user_type = context.get_declared_type_of_symbol(user).unwrap();
        let alias = context
            .store()
            .type_payload(user_type)
            .unwrap()
            .alias()
            .unwrap();

        assert_eq!(context.type_to_string(user_type).unwrap(), "User");
        assert_eq!(
            type_to_string(context.store(), user_type),
            Err(TypeDisplayUnavailable::Alias {
                type_id: user_type,
                alias,
            }),
            "an exported alias cannot be displayed without its retained host proof"
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .insert_symbol(exports, EscapedName::source("User"), other,),
            Some(Some(user))
        );
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().type_alias_len(),
            context.store().mapper_len(),
            context.store().relation_state_snapshot(),
        );

        assert_eq!(
            context.type_to_string(user_type),
            Err(TypeDisplayUnavailable::Alias {
                type_id: user_type,
                alias,
            })
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().type_alias_len(),
                context.store().mapper_len(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
    }

    #[test]
    fn unqualified_named_display_rejects_parent_and_flag_poisons() {
        let mut interface_store = bootstrapped_store();
        let interface = alloc_named_interface(&mut interface_store, "Good");
        let interface_symbol = interface_store
            .type_payload(interface)
            .unwrap()
            .symbol()
            .unwrap();
        let interface_declaration = interface_store
            .symbol(interface_symbol)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let parent = interface_store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::NAMESPACE_MODULE,
                EscapedName::source("Namespace"),
            ))
            .unwrap();
        let mut nested_data =
            SymbolData::new(SymbolFlags::INTERFACE, EscapedName::source("Nested"));
        nested_data.declarations = Some(vec![interface_declaration]);
        nested_data.parent = Some(parent);
        let nested_symbol = interface_store.alloc_symbol(nested_data).unwrap();
        let nested = interface_store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(nested_symbol))
            .unwrap();
        assert!(interface_store.set_declared_type_links(
            nested_symbol,
            crate::semantic::DeclaredTypeLinks {
                declared_type: Some(nested),
                ..crate::semantic::DeclaredTypeLinks::default()
            },
        ));
        assert_eq!(
            type_to_string(&interface_store, nested),
            Err(TypeDisplayUnavailable::MalformedType(nested)),
        );

        let mut alias_store = bootstrapped_store();
        let (object, original_alias) = alloc_named_object_alias(&mut alias_store, "GoodAlias");
        let original_alias_symbol = alias_store
            .type_alias(original_alias)
            .unwrap()
            .symbol()
            .unwrap();
        let alias_declaration = alias_store
            .symbol(original_alias_symbol)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let mut merged_flags_data = SymbolData::new(
            SymbolFlags::TYPE_ALIAS | SymbolFlags::VALUE_MODULE,
            EscapedName::source("BadFlags"),
        );
        merged_flags_data.declarations = Some(vec![alias_declaration]);
        let merged_flags_symbol = alias_store.alloc_symbol(merged_flags_data).unwrap();
        let merged_flags_alias = alias_store
            .alloc_type_alias(Some(merged_flags_symbol))
            .unwrap();
        assert!(alias_store.set_type_alias(object, Some(merged_flags_alias)));
        assert!(alias_store.set_type_alias_links(
            merged_flags_symbol,
            crate::semantic::TypeAliasLinks {
                declared_type: Some(object),
                ..crate::semantic::TypeAliasLinks::default()
            },
        ));
        assert_eq!(
            type_to_string(&alias_store, object),
            Err(TypeDisplayUnavailable::Alias {
                type_id: object,
                alias: merged_flags_alias,
            }),
        );

        let alias_parent = alias_store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::NAMESPACE_MODULE,
                EscapedName::source("AliasNamespace"),
            ))
            .unwrap();
        let mut nested_alias_data =
            SymbolData::new(SymbolFlags::TYPE_ALIAS, EscapedName::source("NestedAlias"));
        nested_alias_data.declarations = Some(vec![alias_declaration]);
        nested_alias_data.parent = Some(alias_parent);
        let nested_alias_symbol = alias_store.alloc_symbol(nested_alias_data).unwrap();
        let nested_alias = alias_store
            .alloc_type_alias(Some(nested_alias_symbol))
            .unwrap();
        assert!(alias_store.set_type_alias(object, Some(nested_alias)));
        assert!(alias_store.set_type_alias_links(
            nested_alias_symbol,
            crate::semantic::TypeAliasLinks {
                declared_type: Some(object),
                ..crate::semantic::TypeAliasLinks::default()
            },
        ));
        assert_eq!(
            type_to_string(&alias_store, object),
            Err(TypeDisplayUnavailable::Alias {
                type_id: object,
                alias: nested_alias,
            }),
        );
    }

    #[test]
    fn host_backed_type_literals_derive_readonly_and_reject_order_drift() {
        let parsed = parse_source_file("type Shape = { readonly first: string; second?: number };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(192);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/host-formatter.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = files.get(&file).unwrap();
        let type_literal = type_alias_body(&parsed, file, "Shape");
        let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(type_literal.node).unwrap().data
        else {
            panic!("expected a type literal")
        };
        let owner = bound.symbol(type_literal).unwrap();
        let properties = literal
            .members
            .nodes
            .iter()
            .map(|member| {
                bound
                    .symbol(NodeRef::new(parsed.arena.id(), file, *member))
                    .unwrap()
            })
            .collect::<Vec<_>>();

        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let (string, number, never) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                (
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.never_type,
                )
            })
            .unwrap();
        assert!(store.set_source_property_readonly(properties[0], true));
        for (property, property_type) in properties.iter().zip([string, number]) {
            assert!(store.set_value_symbol_links(
                *property,
                ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        let members = store.symbol(owner).unwrap().members();
        let object = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::FROM_TYPE_NODE,
                Some(owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            members,
            Some(properties.clone()),
            None,
            None,
            None,
        ));
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();

        assert_eq!(
            type_to_string(&store, object),
            Err(TypeDisplayUnavailable::UnsupportedType {
                type_id: object,
                kind: TypeDataKind::Object,
            }),
        );
        assert_eq!(
            type_to_string_with_host_and_flags(
                &store,
                &host,
                object,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            )
            .unwrap(),
            "{ readonly first: string; second?: number; }",
        );
        assert_eq!(
            get_type_names_for_assignability_error_with_host_and_flags(
                &store,
                &host,
                object,
                never,
                CanonicalTypeFormatFlags::NONE,
            )
            .unwrap(),
            AssignabilityErrorDisplay {
                source: "{ readonly first: string; second?: number; }".into(),
                target: "never".into(),
            },
        );

        assert!(store.set_source_property_readonly(properties[0], false));
        assert_eq!(
            type_to_string_with_host_and_flags(
                &store,
                &host,
                object,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ),
            Err(TypeDisplayUnavailable::MalformedType(object)),
        );
        assert!(store.set_source_property_readonly(properties[0], true));
        assert!(store.set_source_property_readonly(properties[1], true));
        assert_eq!(
            type_to_string_with_host_and_flags(
                &store,
                &host,
                object,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ),
            Err(TypeDisplayUnavailable::MalformedType(object)),
        );
        assert!(store.set_source_property_readonly(properties[1], false));

        let semantic_parent = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("SemanticParent"),
            ))
            .unwrap();
        let owner_declaration = store.symbol(owner).unwrap().declarations().unwrap()[0];
        let mut parented_owner_data = SymbolData::new(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
        );
        parented_owner_data.declarations = Some(vec![owner_declaration]);
        parented_owner_data.members = members;
        parented_owner_data.parent = Some(semantic_parent);
        let parented_owner = store.alloc_symbol(parented_owner_data).unwrap();
        let parented = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::FROM_TYPE_NODE,
                Some(parented_owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            parented,
            members,
            Some(properties.clone()),
            None,
            None,
            None,
        ));
        assert_eq!(
            type_to_string_with_host_and_flags(
                &store,
                &host,
                parented,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ),
            Err(TypeDisplayUnavailable::MalformedType(parented)),
        );

        let drifted = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::FROM_TYPE_NODE,
                Some(owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            drifted,
            members,
            Some(properties.iter().copied().rev().collect()),
            None,
            None,
            None,
        ));
        assert_eq!(
            type_to_string_with_host_and_flags(
                &store,
                &host,
                drifted,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            ),
            Err(TypeDisplayUnavailable::MalformedType(drifted)),
        );
    }

    #[test]
    fn object_literal_clone_tables_format_and_target_poison_fails_closed() {
        let parsed = parse_source_file("const value = { a: 'x', b: 1 }; const empty = {};");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(193);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/object-formatter.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let bindings = binder.finish();
        let object_node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    &record.data,
                    NodeData::ObjectLiteralExpression(object) if !object.properties.nodes.is_empty()
                )
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let empty_node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    &record.data,
                    NodeData::ObjectLiteralExpression(object) if object.properties.nodes.is_empty()
                )
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let NodeData::ObjectLiteralExpression(object_literal) =
            &parsed.arena.get(object_node.node).unwrap().data
        else {
            unreachable!()
        };
        let owner = bindings.file(file).unwrap().symbol(object_node).unwrap();
        let empty_owner = bindings.file(file).unwrap().symbol(empty_node).unwrap();
        let raw_properties = object_literal
            .properties
            .nodes
            .iter()
            .map(|property| {
                bindings
                    .file(file)
                    .unwrap()
                    .symbol(NodeRef::new(parsed.arena.id(), file, *property))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let (symbols, _) = bindings.try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let property_types = store
            .intrinsic_bootstrap()
            .map(|bootstrap| [bootstrap.string_type, bootstrap.number_type])
            .unwrap();

        let result_members = store.alloc_symbol_table();
        let mut clones = Vec::new();
        for (raw, property_type) in raw_properties.iter().zip(property_types) {
            let raw_record = store.symbol(*raw).unwrap();
            let mut data = SymbolData::new(
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                raw_record.name().to_owned(),
            );
            data.declarations = raw_record.declarations().map(<[NodeRef]>::to_vec);
            data.value_declaration = raw_record.value_declaration();
            data.parent = raw_record.parent();
            let name = raw_record.name().as_utf8().unwrap().to_owned();
            let clone = store.alloc_symbol(data).unwrap();
            assert!(store.set_value_symbol_links(
                clone,
                ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    target: Some(*raw),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                store.insert_symbol(result_members, EscapedName::source(&name), clone),
                Some(None),
            );
            clones.push(clone);
        }
        let object = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                Some(owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(result_members),
            Some(clones),
            None,
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, object).unwrap(),
            "{ a: string; b: number; }",
        );

        let empty_members = store.alloc_symbol_table();
        let empty = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                Some(empty_owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            empty,
            Some(empty_members),
            None,
            None,
            None,
            None,
        ));
        assert_eq!(type_to_string(&store, empty).unwrap(), "{}");

        let unowned_members = store.alloc_symbol_table();
        let unowned = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                None,
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            unowned,
            Some(unowned_members),
            None,
            None,
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, unowned),
            Err(TypeDisplayUnavailable::MalformedType(unowned)),
        );

        let poison_members = store.alloc_symbol_table();
        let raw = raw_properties[0];
        let raw_record = store.symbol(raw).unwrap();
        let mut poison_data = SymbolData::new(
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            raw_record.name().to_owned(),
        );
        poison_data.declarations = raw_record.declarations().map(<[NodeRef]>::to_vec);
        poison_data.value_declaration = raw_record.value_declaration();
        poison_data.parent = raw_record.parent();
        let poison_name = raw_record.name().as_utf8().unwrap().to_owned();
        let poison_clone = store.alloc_symbol(poison_data).unwrap();
        assert!(store.set_value_symbol_links(
            poison_clone,
            ValueSymbolLinks {
                resolved_type: Some(property_types[0]),
                target: Some(raw_properties[1]),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.insert_symbol(
                poison_members,
                EscapedName::source(&poison_name),
                poison_clone,
            ),
            Some(None),
        );
        let poisoned = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                Some(owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            poisoned,
            Some(poison_members),
            Some(vec![poison_clone]),
            None,
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, poisoned),
            Err(TypeDisplayUnavailable::MalformedType(poisoned)),
        );
    }

    #[test]
    fn long_object_properties_use_pinned_elision_and_no_truncation() {
        let mut store = bootstrapped_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let names = (0..40)
            .map(|index| format!("p{index:03}"))
            .collect::<Vec<_>>();
        let properties = names
            .iter()
            .map(|name| alloc_typed_property(&mut store, name, string, false, false))
            .collect();
        let object = alloc_structural_object(&mut store, properties);
        let full_parts = names
            .iter()
            .map(|name| format!("{name}: string;"))
            .collect::<Vec<_>>();
        let full = format!("{{ {} }}", full_parts.join(" "));
        let mut truncated_parts = full_parts[..15].to_vec();
        truncated_parts.push("... 24 more ...;".into());
        truncated_parts.push(full_parts.last().unwrap().clone());
        let truncated = format!("{{ {} }}", truncated_parts.join(" "));

        assert_eq!(type_to_string(&store, object).unwrap(), truncated);
        assert_eq!(
            type_to_string_with_flags(
                &store,
                object,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT
                    | CanonicalTypeFormatFlags::NO_TRUNCATION,
            )
            .unwrap(),
            full,
        );
    }

    #[test]
    fn format_flag_bits_and_default_pair_match_the_pinned_enums() {
        assert_eq!(CanonicalTypeFormatFlags::NONE.bits(), 0);
        assert_eq!(CanonicalTypeFormatFlags::NO_TRUNCATION.bits(), 1 << 0);
        assert_eq!(
            CanonicalTypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.bits(),
            1 << 14
        );
        assert_eq!(
            CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE.bits(),
            1 << 20
        );
        assert_eq!(
            CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE.bits(),
            1 << 28
        );
        assert_eq!(
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT.bits(),
            (1 << 14) | (1 << 20)
        );
    }

    #[test]
    fn displays_pinned_intrinsic_prefix_and_boolean_union() {
        let store = bootstrapped_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let cases = [
            (bootstrap.any_type, "any"),
            (bootstrap.auto_type, "any"),
            (bootstrap.error_type, "any"),
            (bootstrap.unresolved_type, "/*unresolved*/ any"),
            (bootstrap.intrinsic_marker_type, "intrinsic"),
            (bootstrap.unknown_type, "unknown"),
            (bootstrap.string_type, "string"),
            (bootstrap.number_type, "number"),
            (bootstrap.bigint_type, "bigint"),
            (bootstrap.boolean_type, "boolean"),
            (bootstrap.es_symbol_type, "symbol"),
            (bootstrap.void_type, "void"),
            (bootstrap.undefined_type, "undefined"),
            (bootstrap.null_type, "null"),
            (bootstrap.never_type, "never"),
            (bootstrap.non_primitive_type, "object"),
        ];
        for (type_id, expected) in cases {
            assert_eq!(type_to_string(&store, type_id).unwrap(), expected);
        }
    }

    #[test]
    fn preserves_pinned_alias_branch_order() {
        let mut store = bootstrapped_store();
        let (any_type, string_type, regular_false_type, regular_true_type) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                (
                    bootstrap.any_type,
                    bootstrap.string_type,
                    bootstrap.regular_false_type,
                    bootstrap.regular_true_type,
                )
            })
            .unwrap();
        let literal_type = store.regular_string_literal_type("value".into()).unwrap();

        let any_alias = attach_type_alias(&mut store, any_type, "AnyAlias");
        let boolean_alias = named_canonical_union(
            &mut store,
            "BooleanAlias",
            &[regular_false_type, regular_true_type],
        );
        attach_type_alias(&mut store, string_type, "StringAlias");
        attach_type_alias(&mut store, literal_type, "LiteralAlias");

        assert_eq!(
            type_to_string(&store, any_type),
            Err(TypeDisplayUnavailable::Alias {
                type_id: any_type,
                alias: any_alias,
            })
        );
        assert_eq!(
            type_to_string(&store, boolean_alias).unwrap(),
            "BooleanAlias"
        );
        assert_eq!(type_to_string(&store, string_type).unwrap(), "string");
        assert_eq!(type_to_string(&store, literal_type).unwrap(), "\"value\"");
    }

    #[test]
    fn displays_regular_and_fresh_literal_pairs_identically() {
        let mut store = bootstrapped_store();
        let string = store
            .regular_string_literal_type("quoted\"\n".into())
            .unwrap();
        let number = store
            .regular_number_literal_type(Number::new(-42.5))
            .unwrap();
        let bigint = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("-123n"))
            .unwrap();
        for (regular, expected) in [
            (string, "\"quoted\\\"\\n\""),
            (number, "-42.5"),
            (bigint, "-123n"),
        ] {
            let fresh = fresh_literal(&store, regular);
            assert_eq!(type_to_string(&store, regular).unwrap(), expected);
            assert_eq!(type_to_string(&store, fresh).unwrap(), expected);
        }
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        for (regular, fresh, expected) in [
            (bootstrap.regular_false_type, bootstrap.false_type, "false"),
            (bootstrap.regular_true_type, bootstrap.true_type, "true"),
        ] {
            assert_eq!(type_to_string(&store, regular).unwrap(), expected);
            assert_eq!(type_to_string(&store, fresh).unwrap(), expected);
        }
    }

    #[test]
    fn displays_canonical_primitive_literal_and_nullable_unions_in_pinned_order() {
        let mut store = strict_bootstrapped_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (undefined, null, string, number) = (
            bootstrap.undefined_type,
            bootstrap.null_type,
            bootstrap.string_type,
            bootstrap.number_type,
        );
        let primitive = canonical_union(&mut store, &[number, string]);
        assert_eq!(
            type_to_string(&store, primitive).unwrap(),
            "string | number"
        );

        let text = store.regular_string_literal_type("x".into()).unwrap();
        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("2n"))
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (regular_false, regular_true) =
            (bootstrap.regular_false_type, bootstrap.regular_true_type);
        let literal_nullable = canonical_union(
            &mut store,
            &[regular_true, null, two, text, undefined, regular_false, one],
        );
        assert_eq!(
            type_to_string(&store, literal_nullable).unwrap(),
            "\"x\" | 1 | 2n | boolean | null | undefined"
        );
    }

    #[test]
    fn preserves_named_union_aliases_and_denormalized_cache_origins_without_writes() {
        let mut store = bootstrapped_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, bigint) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.bigint_type,
        );
        let anonymous = canonical_union(&mut store, &[number, string]);
        let scalar = named_canonical_union(&mut store, "Scalar", &[number, string]);
        let outer = canonical_union(&mut store, &[scalar, bigint]);
        let repeated = canonical_union(&mut store, &[bigint, scalar]);

        assert_ne!(anonymous, scalar);
        assert_eq!(outer, repeated);
        assert!(matches!(
            store.type_payload(outer).unwrap().data(),
            TypeData::Union(data) if data.origin.is_some()
        ));

        let before = (
            store.type_len(),
            store.symbol_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.union_cache_validation_scan_count(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            type_to_string(&store, anonymous).unwrap(),
            "string | number"
        );
        assert_eq!(type_to_string(&store, scalar).unwrap(), "Scalar");
        assert_eq!(
            type_to_string_with_flags(&store, scalar, CanonicalTypeFormatFlags::NONE).unwrap(),
            "Scalar"
        );
        assert_eq!(type_to_string(&store, outer).unwrap(), "bigint | Scalar");
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.union_cache_validation_scan_count(),
                store.relation_state_snapshot(),
            ),
            before
        );
    }

    #[test]
    fn canonical_union_display_flows_through_assignability_diagnostics() {
        let mut store = bootstrapped_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, bigint) = (bootstrap.number_type, bootstrap.bigint_type);
        let source = store
            .regular_string_literal_type("not numeric".into())
            .unwrap();
        let anonymous = canonical_union(&mut store, &[bigint, number]);
        let named = named_canonical_union(&mut store, "Numeric", &[bigint, number]);

        assert_eq!(
            get_type_names_for_assignability_error(&store, source, anonymous).unwrap(),
            AssignabilityErrorDisplay {
                source: "string".into(),
                target: "number | bigint".into(),
            }
        );
        assert_eq!(
            get_type_names_for_assignability_error(&store, source, named).unwrap(),
            AssignabilityErrorDisplay {
                source: "string".into(),
                target: "Numeric".into(),
            }
        );
    }

    #[test]
    fn long_canonical_union_uses_pinned_elision_and_no_truncation() {
        let mut store = bootstrapped_store();
        let values: Vec<_> = (0..40).map(|index| format!("v{index:03}")).collect();
        let literals: Vec<_> = values
            .iter()
            .map(|value| store.regular_string_literal_type(value.clone()).unwrap())
            .collect();
        let union = canonical_union(&mut store, &literals);
        let never = store.intrinsic_bootstrap().unwrap().never_type;

        let full_parts: Vec<_> = values.iter().map(|value| format!("\"{value}\"")).collect();
        let full = full_parts.join(" | ");
        let mut truncated_parts = full_parts[..21].to_vec();
        truncated_parts.push("... 18 more ...".into());
        truncated_parts.push(full_parts.last().unwrap().clone());
        let truncated = truncated_parts.join(" | ");

        assert_eq!(type_to_string(&store, union).unwrap(), truncated);
        let no_truncation = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT
            | CanonicalTypeFormatFlags::NO_TRUNCATION;
        assert_eq!(
            type_to_string_with_flags(&store, union, no_truncation).unwrap(),
            full
        );
        assert_eq!(
            get_type_names_for_assignability_error(&store, never, union).unwrap(),
            AssignabilityErrorDisplay {
                source: "never".into(),
                target: truncated,
            }
        );
        assert_eq!(
            get_type_names_for_assignability_error_with_flags(
                &store,
                never,
                union,
                CanonicalTypeFormatFlags::NO_TRUNCATION,
            )
            .unwrap(),
            AssignabilityErrorDisplay {
                source: "never".into(),
                target: full,
            }
        );
    }

    #[test]
    fn malformed_and_cyclic_unions_fail_typed_without_formatter_writes() {
        let mut invalid_store = bootstrapped_store();
        let bootstrap = invalid_store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let invalid = invalid_store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        let invalid_before = (
            invalid_store.type_len(),
            invalid_store.symbol_len(),
            invalid_store.type_alias_len(),
            invalid_store.mapper_len(),
            invalid_store.union_cache_validation_scan_count(),
            invalid_store.relation_state_snapshot(),
        );
        assert_eq!(
            type_to_string(&invalid_store, invalid),
            Err(TypeDisplayUnavailable::InvalidUnion(invalid))
        );
        assert_eq!(
            (
                invalid_store.type_len(),
                invalid_store.symbol_len(),
                invalid_store.type_alias_len(),
                invalid_store.mapper_len(),
                invalid_store.union_cache_validation_scan_count(),
                invalid_store.relation_state_snapshot(),
            ),
            invalid_before
        );

        let mut cyclic_store = bootstrapped_store();
        let bootstrap = cyclic_store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let cyclic = canonical_union(&mut cyclic_store, &[string, number]);
        assert!(cyclic_store.set_union_caches(
            cyclic,
            None,
            None,
            Some(cyclic),
            EscapedName::default(),
            ConstituentMapState::Unallocated,
        ));
        let cyclic_before = (
            cyclic_store.type_len(),
            cyclic_store.symbol_len(),
            cyclic_store.type_alias_len(),
            cyclic_store.mapper_len(),
            cyclic_store.union_cache_validation_scan_count(),
            cyclic_store.relation_state_snapshot(),
        );
        assert_eq!(
            type_to_string(&cyclic_store, cyclic),
            Err(TypeDisplayUnavailable::CyclicType(cyclic))
        );
        assert_eq!(
            (
                cyclic_store.type_len(),
                cyclic_store.symbol_len(),
                cyclic_store.type_alias_len(),
                cyclic_store.mapper_len(),
                cyclic_store.union_cache_validation_scan_count(),
                cyclic_store.relation_state_snapshot(),
            ),
            cyclic_before
        );
    }

    #[test]
    fn uses_pinned_quote_selection_and_escaping() {
        let mut store = bootstrapped_store();
        let value = "double\" single' slash\\ nul\0\u{0007}\u{0085}\u{2028} 1\0";
        let literal = store.regular_string_literal_type(value.into()).unwrap();
        assert_eq!(
            type_to_string(&store, literal).unwrap(),
            "\"double\\\" single' slash\\\\ nul\\0\\u0007\\u0085\\u2028 1\\0\""
        );
        assert_eq!(
            type_to_string_with_flags(
                &store,
                literal,
                CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                    | CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE,
            )
            .unwrap(),
            "'double\" single\\' slash\\\\ nul\\0\\u0007\\u0085\\u2028 1\\0'"
        );

        let followed_by_digit = store
            .regular_string_literal_type(concat!("\0", "1", "\0").into())
            .unwrap();
        assert_eq!(
            type_to_string(&store, followed_by_digit).unwrap(),
            "\"\\x001\\0\""
        );
    }

    #[test]
    fn formats_the_complete_pinned_number_literal_domain() {
        let mut store = bootstrapped_store();
        let cases = [
            (Number::new(-0.0), "0"),
            (Number::nan(), "NaN"),
            (Number::infinity(1), "Infinity"),
            (Number::infinity(-1), "-Infinity"),
            (Number::new(1e21), "1e+21"),
            (Number::new(5e-324), "5e-324"),
        ];
        for (value, expected) in cases {
            let literal = store
                .alloc_literal_type(
                    TypeFlags::NUMBER_LITERAL,
                    LiteralValue::Number(value),
                    RegularLiteralLink::SelfType,
                )
                .unwrap();
            assert_eq!(type_to_string(&store, literal).unwrap(), expected);
        }

        let nan = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::nan()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let string_type = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            get_type_names_for_assignability_error(&store, nan, string_type).unwrap(),
            AssignabilityErrorDisplay {
                source: "number".into(),
                target: "string".into(),
            }
        );
    }

    #[test]
    fn rejects_invalid_literal_links() {
        let mut store = bootstrapped_store();
        let regular = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(7.0)),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let incomplete_fresh = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(7.0)),
                RegularLiteralLink::Type(regular),
            )
            .unwrap();
        assert_eq!(
            type_to_string(&store, incomplete_fresh),
            Err(TypeDisplayUnavailable::InvalidLiteralLinks(
                incomplete_fresh
            ))
        );
        assert!(store.set_literal_links(regular, Some(regular), regular));
        assert_eq!(
            type_to_string(&store, regular),
            Err(TypeDisplayUnavailable::InvalidLiteralLinks(regular))
        );
    }

    #[test]
    fn applies_pinned_ascii_truncation_and_fails_closed_on_split_utf8() {
        let mut store = bootstrapped_store();
        let long = store.regular_string_literal_type("x".repeat(400)).unwrap();
        let displayed = type_to_string(&store, long).unwrap();
        assert_eq!(displayed.len(), 320);
        assert!(displayed.starts_with('"'));
        assert!(displayed.ends_with("..."));
        assert_eq!(displayed.matches('x').count(), 316);
        let complete = type_to_string_with_flags(
            &store,
            long,
            CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                | CanonicalTypeFormatFlags::NO_TRUNCATION,
        )
        .unwrap();
        assert_eq!(complete, format!("\"{}\"", "x".repeat(400)));

        let split = store
            .regular_string_literal_type(format!("{}é{}", "x".repeat(315), "x".repeat(10)))
            .unwrap();
        assert_eq!(
            type_to_string(&store, split),
            Err(TypeDisplayUnavailable::Utf8TruncationBoundary {
                type_id: split,
                boundary: 317,
            })
        );
    }

    #[test]
    fn truncation_uses_the_exact_ordinary_and_hard_byte_boundaries() {
        let mut store = bootstrapped_store();
        let ordinary_below = store.regular_string_literal_type("x".repeat(317)).unwrap();
        let ordinary_at = store.regular_string_literal_type("x".repeat(318)).unwrap();
        assert_eq!(
            type_to_string(&store, ordinary_below).unwrap(),
            format!("\"{}\"", "x".repeat(317))
        );
        assert_eq!(
            type_to_string(&store, ordinary_at).unwrap(),
            format!("\"{}...", "x".repeat(316))
        );

        let hard_below = store
            .regular_string_literal_type("x".repeat(1_999_997))
            .unwrap();
        let hard_at = store
            .regular_string_literal_type("x".repeat(1_999_998))
            .unwrap();
        let no_truncation = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT
            | CanonicalTypeFormatFlags::NO_TRUNCATION;
        assert_eq!(
            type_to_string_with_flags(&store, hard_below, no_truncation).unwrap(),
            format!("\"{}\"", "x".repeat(1_999_997))
        );
        let hard_display = type_to_string_with_flags(&store, hard_at, no_truncation).unwrap();
        assert_eq!(hard_display.len(), 2_000_000);
        assert_eq!(hard_display, format!("\"{}...", "x".repeat(1_999_996)));
    }

    #[test]
    fn context_no_error_truncation_controls_default_explicit_and_ts2322_display() {
        let value = "x".repeat(400);
        let parsed = parse_source_file(&format!("type Long = \"{value}\";"));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(93);
        let long_node = type_alias_body(&parsed, file, "Long");
        let complete = format!("\"{value}\"");
        let truncated = format!("\"{}...", "x".repeat(316));

        let mut default_context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let default_long = default_context.get_type_from_type_node(long_node).unwrap();
        let default_never = default_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .never_type;
        assert!(!default_context.options().no_error_truncation);
        assert_eq!(
            default_context.type_to_string(default_long).unwrap(),
            truncated
        );
        assert_eq!(
            default_context
                .type_to_string_with_flags(default_long, CanonicalTypeFormatFlags::NO_TRUNCATION,)
                .unwrap(),
            complete
        );
        assert_eq!(
            default_context
                .get_type_names_for_assignability_error(default_long, default_never)
                .unwrap(),
            AssignabilityErrorDisplay {
                source: truncated,
                target: "never".into(),
            }
        );

        let mut complete_context = parsed_context(
            &parsed,
            file,
            CanonicalCheckerOptions {
                no_error_truncation: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let complete_long = complete_context.get_type_from_type_node(long_node).unwrap();
        let complete_never = complete_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .never_type;
        assert!(complete_context.options().no_error_truncation);
        assert_eq!(
            complete_context.type_to_string(complete_long).unwrap(),
            complete
        );
        assert_eq!(
            complete_context
                .type_to_string_with_flags(complete_long, CanonicalTypeFormatFlags::NONE)
                .unwrap(),
            complete
        );
        assert_eq!(
            complete_context
                .type_to_string_with_flags(
                    complete_long,
                    CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE,
                )
                .unwrap(),
            format!("'{value}'")
        );
        assert_eq!(
            complete_context
                .get_type_names_for_assignability_error(complete_long, complete_never)
                .unwrap(),
            AssignabilityErrorDisplay {
                source: complete,
                target: "never".into(),
            }
        );
    }

    #[test]
    fn unique_symbol_is_flag_gated_and_noncanonical_unions_are_rejected() {
        let mut store = bootstrapped_store();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                EscapedName::source("token"),
            ))
            .unwrap();
        let unique = store.alloc_unique_es_symbol_type(symbol).unwrap();
        assert_eq!(type_to_string(&store, unique).unwrap(), "unique symbol");
        assert_eq!(
            type_to_string_with_flags(&store, unique, CanonicalTypeFormatFlags::NONE),
            Err(TypeDisplayUnavailable::UniqueSymbolName(unique))
        );

        let (string_type, number_type) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| (bootstrap.string_type, bootstrap.number_type))
            .unwrap();
        assert_eq!(
            get_type_names_for_assignability_error(&store, unique, string_type),
            Err(TypeDisplayUnavailable::UniqueSymbolName(unique))
        );
        let union = store
            .alloc_union_type(
                crate::semantic::types::ObjectFlags::PRIMITIVE_UNION,
                vec![string_type, number_type],
            )
            .unwrap();
        assert_eq!(
            type_to_string(&store, union),
            Err(TypeDisplayUnavailable::InvalidUnion(union))
        );
    }

    #[test]
    fn assignability_error_display_generalizes_only_without_singleton_target() {
        let mut store = bootstrapped_store();
        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two = store.regular_number_literal_type(Number::new(2.0)).unwrap();
        let fresh_one = fresh_literal(&store, one);
        let fresh_two = fresh_literal(&store, two);
        let text = store.regular_string_literal_type("text".into()).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_eq!(
            get_type_names_for_assignability_error(&store, fresh_one, bootstrap.string_type,)
                .unwrap(),
            AssignabilityErrorDisplay {
                source: "number".into(),
                target: "string".into(),
            }
        );
        assert_eq!(
            get_type_names_for_assignability_error(&store, fresh_two, one).unwrap(),
            AssignabilityErrorDisplay {
                source: "2".into(),
                target: "1".into(),
            }
        );
        assert_eq!(
            get_type_names_for_assignability_error(&store, text, bootstrap.never_type).unwrap(),
            AssignabilityErrorDisplay {
                source: "\"text\"".into(),
                target: "never".into(),
            }
        );
        assert_eq!(
            get_type_names_for_assignability_error(
                &store,
                bootstrap.true_type,
                bootstrap.string_type,
            )
            .unwrap(),
            AssignabilityErrorDisplay {
                source: "boolean".into(),
                target: "string".into(),
            }
        );

        let pair = get_type_names_for_assignability_error(&store, fresh_one, bootstrap.string_type)
            .unwrap();
        let diagnostic =
            Diagnostic::with_arguments(message_by_code(2322).unwrap(), [pair.source, pair.target]);
        assert_eq!(
            diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
    }

    #[test]
    fn parsed_function_display_uses_semantic_parameter_types_and_syntactic_optionality() {
        let parsed = parse_source_file(concat!(
            "type Result = string | number; ",
            "type Alias = (value?: number) => Result; ",
            "let direct: (required: string, optional?: number) => Result;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(206);
        let mut context = parsed_context(
            &parsed,
            file,
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
        );

        let alias_node = type_alias_body(&parsed, file, "Alias");
        let alias_type = context.get_type_from_type_node(alias_node).unwrap();
        assert_eq!(context.type_to_string(alias_type).unwrap(), "Alias");

        let direct_node = variable_type_node(&parsed, file, "direct");
        let direct_type = context.get_type_from_type_node(direct_node).unwrap();
        assert_eq!(
            context.type_to_string(direct_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: direct_type,
                reason: FunctionTypeDisplayUnavailable::UnresolvedReturn,
            })
        );
        let signature = function_signature(&context, direct_node).unwrap();
        context.get_return_type_of_signature(signature).unwrap();
        assert_eq!(
            context.type_to_string(direct_type).unwrap(),
            "(required: string, optional?: number | undefined) => Result",
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            context
                .get_type_names_for_assignability_error(direct_type, string)
                .unwrap(),
            AssignabilityErrorDisplay {
                source: "(required: string, optional?: number | undefined) => Result".into(),
                target: "string".into(),
            },
        );
        let optional_parameter = match &parsed.arena.get(direct_node.node).unwrap().data {
            NodeData::FunctionTypeNode(function) => NodeRef::new(
                direct_node.arena,
                direct_node.file,
                function.parameters.nodes[1],
            ),
            _ => unreachable!(),
        };
        let parameter_symbol = context
            .file(file)
            .unwrap()
            .1
            .symbol(optional_parameter)
            .unwrap();
        let resolved_optional = context
            .store()
            .value_symbol_links(parameter_symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert!(
            context
                .store()
                .type_payload(resolved_optional)
                .is_some_and(|record| record.flags().intersects(TypeFlags::UNION)),
            "display must use this optional value union together with syntactic `?`",
        );
    }

    #[test]
    fn function_display_traverses_parameters_before_demanding_the_outer_return() {
        let parsed =
            parse_source_file("let outer: (callback: (value: string) => number) => boolean;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(213);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let outer_node = variable_type_node(&parsed, file, "outer");
        let outer_type = context.get_type_from_type_node(outer_node).unwrap();
        let callback_symbol = function_parameter_symbol(&context, &parsed, outer_node, 0);
        let callback_type = context
            .store()
            .value_symbol_links(callback_symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_ne!(callback_type, outer_type);

        assert_eq!(
            context.type_to_string(outer_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: callback_type,
                reason: FunctionTypeDisplayUnavailable::UnresolvedReturn,
            })
        );

        let callback_node = context
            .store()
            .type_payload(callback_type)
            .and_then(TypeRecord::symbol)
            .and_then(|symbol| context.store().symbol(symbol))
            .and_then(|symbol| match symbol.declarations() {
                Some([declaration]) => Some(*declaration),
                _ => None,
            })
            .unwrap();
        let callback_signature = function_signature(&context, callback_node).unwrap();
        context
            .get_return_type_of_signature(callback_signature)
            .unwrap();
        assert_eq!(
            context.type_to_string(outer_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: outer_type,
                reason: FunctionTypeDisplayUnavailable::UnresolvedReturn,
            })
        );

        let outer_signature = function_signature(&context, outer_node).unwrap();
        context
            .get_return_type_of_signature(outer_signature)
            .unwrap();
        assert_eq!(
            context.type_to_string(outer_type).unwrap(),
            "(callback: (value: string) => number) => boolean"
        );
    }

    #[test]
    fn aliased_function_display_rejects_backtracking_and_malformed_cache_states() {
        let parsed = parse_source_file(concat!(
            "type Barrier = (value: string) => number; ",
            "type Parameters = (value: string) => number; ",
            "type Poisoned = (value: string) => number;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(209);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let barrier_node = type_alias_body(&parsed, file, "Barrier");
        let parameters_node = type_alias_body(&parsed, file, "Parameters");
        let poisoned_node = type_alias_body(&parsed, file, "Poisoned");
        let barrier = context.get_type_from_type_node(barrier_node).unwrap();
        let parameters = context.get_type_from_type_node(parameters_node).unwrap();
        let poisoned = context.get_type_from_type_node(poisoned_node).unwrap();
        assert_eq!(context.type_to_string(barrier).unwrap(), "Barrier");
        assert_eq!(context.type_to_string(parameters).unwrap(), "Parameters");
        assert_eq!(context.type_to_string(poisoned).unwrap(), "Poisoned");

        let barrier_parameter = function_parameter_symbol(&context, &parsed, barrier_node, 0);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(barrier_parameter, ValueSymbolLinks::default(),)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_structured_type_members(barrier, None, None, None, None, None,)
        );
        assert_eq!(
            context.type_to_string(barrier),
            Err(TypeDisplayUnavailable::MalformedType(barrier))
        );

        let pending_parameter = function_parameter_symbol(&context, &parsed, parameters_node, 0);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(pending_parameter, ValueSymbolLinks::default(),)
        );
        assert_eq!(
            context.type_to_string(parameters),
            Err(TypeDisplayUnavailable::MalformedType(parameters))
        );

        let poisoned_parameter = function_parameter_symbol(&context, &parsed, poisoned_node, 0);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            poisoned_parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                target: Some(poisoned_parameter),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            context.type_to_string(poisoned),
            Err(TypeDisplayUnavailable::MalformedType(poisoned))
        );
    }

    #[test]
    fn parsed_nested_function_union_and_array_display_preserve_precedence() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Result = string | number; ",
            "type Callback = (value: string) => number; ",
            "let nested: (callback: (value: string) => number) => () => Result; ",
            "let mixed: string | ((value: string) => number); ",
            "let list: ((value: string) => number)[]; ",
            "let named: string | Callback;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(207);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let nested = context
            .get_type_from_type_node(variable_type_node(&parsed, file, "nested"))
            .unwrap();
        let mixed = context
            .get_type_from_type_node(variable_type_node(&parsed, file, "mixed"))
            .unwrap();
        let list = context
            .get_type_from_type_node(variable_type_node(&parsed, file, "list"))
            .unwrap();
        let named = context
            .get_type_from_type_node(variable_type_node(&parsed, file, "named"))
            .unwrap();
        resolve_all_function_returns(&mut context, &parsed, file);

        assert_eq!(
            context.type_to_string(nested).unwrap(),
            "(callback: (value: string) => number) => () => Result",
        );
        assert_eq!(
            context.type_to_string(mixed).unwrap(),
            "string | ((value: string) => number)",
        );
        assert_eq!(
            context.type_to_string(list).unwrap(),
            "((value: string) => number)[]",
        );
        let named = context.type_to_string(named).unwrap();
        assert!(named.contains("Callback"));
        assert!(!named.contains("(Callback)"));
    }

    #[test]
    fn parsed_function_display_rejects_poisoned_parameter_value_cache() {
        let parsed = parse_source_file("let fn: (value: string) => number;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(208);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let function = variable_type_node(&parsed, file, "fn");
        let type_ = context.get_type_from_type_node(function).unwrap();
        resolve_all_function_returns(&mut context, &parsed, file);
        assert_eq!(
            context.type_to_string(type_).unwrap(),
            "(value: string) => number"
        );

        let parameter = match &parsed.arena.get(function.node).unwrap().data {
            NodeData::FunctionTypeNode(data) => {
                NodeRef::new(function.arena, function.file, data.parameters.nodes[0])
            }
            _ => unreachable!(),
        };
        let parameter_symbol = context.file(file).unwrap().1.symbol(parameter).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            parameter_symbol,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            context.type_to_string(type_),
            Err(TypeDisplayUnavailable::MalformedType(type_))
        );
    }

    #[test]
    fn unbranded_callable_shapes_remain_explicit_boundaries() {
        let mut store = bootstrapped_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let first = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();
        let second = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();
        let construct_signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::CONSTRUCT,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();
        let unvalidated = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            unvalidated,
            None,
            Some(Vec::new()),
            Some(vec![first]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, unvalidated),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: unvalidated,
                reason: FunctionTypeDisplayUnavailable::UnvalidatedCallable,
            })
        );

        let property = alloc_typed_property(&mut store, "value", number, false, false);
        let callable_with_property = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let property_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(property_members, EscapedName::source("value"), property,),
            Some(None),
        );
        assert!(store.set_structured_type_members(
            callable_with_property,
            Some(property_members),
            Some(vec![property]),
            Some(vec![first]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, callable_with_property),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: callable_with_property,
                reason: FunctionTypeDisplayUnavailable::CallableProperties,
            })
        );

        let overloaded = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            overloaded,
            None,
            Some(Vec::new()),
            Some(vec![first, second]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, overloaded),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: overloaded,
                reason: FunctionTypeDisplayUnavailable::Overloads,
            })
        );

        let repeated_inherited_signature = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            repeated_inherited_signature,
            None,
            Some(Vec::new()),
            Some(vec![first, first]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, repeated_inherited_signature),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: repeated_inherited_signature,
                reason: FunctionTypeDisplayUnavailable::Overloads,
            })
        );

        let construct = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            construct,
            None,
            Some(Vec::new()),
            None,
            Some(vec![construct_signature]),
            None,
        ));
        assert_eq!(
            type_to_string(&store, construct),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: construct,
                reason: FunctionTypeDisplayUnavailable::ConstructSignatures,
            })
        );

        let rest_parameter = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("values"),
            ))
            .unwrap();
        let rest_signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::HAS_REST_PARAMETER,
                None,
                Vec::new(),
                None,
                vec![rest_parameter],
                Some(number),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_resolved_min_argument_count(rest_signature, 2));
        let rest_callable = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            rest_callable,
            None,
            Some(Vec::new()),
            Some(vec![rest_signature]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, rest_callable),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: rest_callable,
                reason: FunctionTypeDisplayUnavailable::RestParameter,
            })
        );

        let index = store
            .alloc_index_info(number, number, false, None, Vec::new())
            .unwrap();
        let indexed = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            indexed,
            None,
            Some(Vec::new()),
            None,
            None,
            Some(vec![index]),
        ));
        assert_eq!(
            type_to_string(&store, indexed),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: indexed,
                reason: FunctionTypeDisplayUnavailable::IndexSignatures,
            })
        );
    }

    #[test]
    fn source_callable_member_tables_preserve_typed_capability_boundaries() {
        let parsed = parse_source_file(concat!(
            "type Callable = { (): number; }; ",
            "type Constructable = { new (): object; }; ",
            "type Indexed = { [key: string]: number; };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(210);
        let mut context = parsed_context(&parsed, file, CanonicalCheckerOptions::default());
        let (call_literal, call_declaration) =
            type_literal_member(&parsed, file, "Callable", SyntaxKind::CallSignature);
        let (construct_literal, construct_declaration) = type_literal_member(
            &parsed,
            file,
            "Constructable",
            SyntaxKind::ConstructSignature,
        );
        let (index_literal, index_declaration) =
            type_literal_member(&parsed, file, "Indexed", SyntaxKind::IndexSignature);
        let bound = &context.file(file).unwrap().1;
        let call_owner = bound.symbol(call_literal).unwrap();
        let construct_owner = bound.symbol(construct_literal).unwrap();
        let index_owner = bound.symbol(index_literal).unwrap();
        let call_members = context
            .store()
            .symbol(call_owner)
            .unwrap()
            .members()
            .unwrap();
        let construct_members = context
            .store()
            .symbol(construct_owner)
            .unwrap()
            .members()
            .unwrap();
        let index_members = context
            .store()
            .symbol(index_owner)
            .unwrap()
            .members()
            .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;

        let store = context.store_mut_for_test();
        let call_signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::NONE,
                Some(call_declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();
        let call_type = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(call_owner))
            .unwrap();
        assert!(store.set_structured_type_members(
            call_type,
            Some(call_members),
            Some(Vec::new()),
            Some(vec![call_signature]),
            None,
            None,
        ));

        let construct_signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::CONSTRUCT,
                Some(construct_declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();
        let construct_type = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(construct_owner))
            .unwrap();
        assert!(store.set_structured_type_members(
            construct_type,
            Some(construct_members),
            Some(Vec::new()),
            None,
            Some(vec![construct_signature]),
            None,
        ));

        let index_info = store
            .alloc_index_info(string, number, false, Some(index_declaration), Vec::new())
            .unwrap();
        let index_type = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(index_owner))
            .unwrap();
        assert!(store.set_structured_type_members(
            index_type,
            Some(index_members),
            Some(Vec::new()),
            None,
            None,
            Some(vec![index_info]),
        ));

        assert_eq!(
            type_to_string(context.store(), call_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: call_type,
                reason: FunctionTypeDisplayUnavailable::UnvalidatedCallable,
            })
        );
        assert_eq!(
            type_to_string(context.store(), construct_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: construct_type,
                reason: FunctionTypeDisplayUnavailable::ConstructSignatures,
            })
        );
        assert_eq!(
            type_to_string(context.store(), index_type),
            Err(TypeDisplayUnavailable::FunctionType {
                type_id: index_type,
                reason: FunctionTypeDisplayUnavailable::IndexSignatures,
            })
        );
    }

    #[test]
    fn malformed_unbranded_callable_caches_fail_before_capability_classification() {
        let mut store = bootstrapped_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                0,
            )
            .unwrap();

        let property = alloc_typed_property(&mut store, "value", number, false, false);
        let malformed_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(malformed_members, EscapedName::source("notValue"), property,),
            Some(None),
        );
        let malformed_properties = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            malformed_properties,
            Some(malformed_members),
            Some(vec![property]),
            Some(vec![signature]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, malformed_properties),
            Err(TypeDisplayUnavailable::MalformedType(malformed_properties,))
        );

        let duplicate_properties = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let duplicate_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(duplicate_members, EscapedName::source("value"), property,),
            Some(None),
        );
        assert!(store.set_structured_type_members(
            duplicate_properties,
            Some(duplicate_members),
            Some(vec![property, property]),
            Some(vec![signature]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, duplicate_properties),
            Err(TypeDisplayUnavailable::MalformedType(duplicate_properties,))
        );

        let invalid_call_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::internal(InternalSymbolName::Call),
            ))
            .unwrap();
        let invalid_call_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(
                invalid_call_members,
                EscapedName::internal(InternalSymbolName::Call),
                invalid_call_symbol,
            ),
            Some(None),
        );
        let invalid_call_table = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            invalid_call_table,
            Some(invalid_call_members),
            Some(Vec::new()),
            Some(vec![signature]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, invalid_call_table),
            Err(TypeDisplayUnavailable::MalformedType(invalid_call_table))
        );

        let malformed_signature = store
            .alloc_signature(
                crate::semantic::signatures::SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(number),
                None,
                -1,
            )
            .unwrap();
        let malformed_overload = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            malformed_overload,
            None,
            Some(Vec::new()),
            Some(vec![signature, malformed_signature]),
            None,
            None,
        ));
        assert_eq!(
            type_to_string(&store, malformed_overload),
            Err(TypeDisplayUnavailable::MalformedType(malformed_overload))
        );

        let index = store
            .alloc_index_info(number, number, false, None, Vec::new())
            .unwrap();
        let malformed_indexes = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            malformed_indexes,
            None,
            Some(Vec::new()),
            None,
            None,
            Some(vec![index, index]),
        ));
        assert_eq!(
            type_to_string(&store, malformed_indexes),
            Err(TypeDisplayUnavailable::MalformedType(malformed_indexes))
        );
    }

    #[test]
    fn parsed_parentheses_and_primitive_aliases_erase_to_the_same_display_identity() {
        let parsed = parse_source_file(
            r#"type Wrapped = (string);
type Quoted = ("quoted\"\n");"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(92);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/formatter.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let mut aliases = parsed.arena.iter().filter_map(|(_, node)| {
            let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                return None;
            };
            let name = match &parsed.arena.get(alias.name)?.data {
                NodeData::Identifier(name) => name.text.as_str(),
                _ => return None,
            };
            Some((name, NodeRef::new(parsed.arena.id(), file, alias.type_)))
        });
        let wrapped = aliases.find(|(name, _)| *name == "Wrapped").unwrap().1;
        let quoted = aliases.find(|(name, _)| *name == "Quoted").unwrap().1;
        let wrapped_type = context.get_type_from_type_node(wrapped).unwrap();
        let quoted_type = context.get_type_from_type_node(quoted).unwrap();
        assert_eq!(context.type_to_string(wrapped_type).unwrap(), "string");
        assert_eq!(
            context.type_to_string(quoted_type).unwrap(),
            "\"quoted\\\"\\n\""
        );
        assert_eq!(
            parsed.arena.get(wrapped.node).unwrap().kind,
            SyntaxKind::ParenthesizedType
        );
    }
}
