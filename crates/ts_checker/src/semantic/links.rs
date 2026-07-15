//! Sparse checker-owned link records.
//!
//! typescript-go deliberately splits checker caches across many typed
//! `core.LinkStore`s.  This module ports the dependency-closed common slice;
//! it does not reintroduce the old monolithic `SymbolLinks` / `TypeLinks`
//! shape.  Link values are read as immutable snapshots and committed by
//! replacement, so recursive checker work never has to retain `&mut` access
//! to a cache record.

use std::{
    collections::HashMap,
    hash::Hash,
    marker::PhantomData,
    num::NonZeroU64,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not},
    sync::atomic::{AtomicU64, Ordering},
};

use ts_ast::NodeRef;
use ts_binder::{EscapedName, SemanticStoreId, SemanticSymbolId, SymbolFlags};

use super::{SignatureId, TypeId, TypeMapperId, type_records::CacheHashKey, types::VarianceFlags};

/// Three-valued state used by lazy checker decisions.
///
/// Numeric values and predicates match `internal/core/tristate.go` at the
/// pinned typescript-go revision.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum Tristate {
    #[default]
    Unknown = 0,
    False = 1,
    True = 2,
}

impl Tristate {
    #[must_use]
    pub const fn is_true(self) -> bool {
        matches!(self, Self::True)
    }

    #[must_use]
    pub const fn is_true_or_unknown(self) -> bool {
        matches!(self, Self::True | Self::Unknown)
    }

    #[must_use]
    pub const fn is_false(self) -> bool {
        matches!(self, Self::False)
    }

    #[must_use]
    pub const fn is_false_or_unknown(self) -> bool {
        matches!(self, Self::False | Self::Unknown)
    }

    #[must_use]
    pub const fn is_unknown(self) -> bool {
        matches!(self, Self::Unknown)
    }

    #[must_use]
    pub const fn default_if_unknown(self, value: Self) -> Self {
        if self.is_unknown() { value } else { self }
    }
}

impl From<bool> for Tristate {
    fn from(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

/// Checker-only node flags.
///
/// The holes are intentional and preserve the exact upstream bit positions.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct NodeCheckFlags(u32);

impl NodeCheckFlags {
    pub const NONE: Self = Self(0);
    pub const TYPE_CHECKED: Self = Self(1 << 0);
    pub const CONTEXT_CHECKED: Self = Self(1 << 6);
    pub const ENUM_VALUES_COMPUTED: Self = Self(1 << 10);
    pub const ASSIGNMENTS_MARKED: Self = Self(1 << 17);
    pub const CONTAINS_CLASS_WITH_PRIVATE_IDENTIFIERS: Self = Self(1 << 20);
    pub const CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER: Self = Self(1 << 21);
    pub const IN_CHECK_IDENTIFIER: Self = Self(1 << 22);
    pub const INITIALIZER_IS_UNDEFINED: Self = Self(1 << 24);
    pub const INITIALIZER_IS_UNDEFINED_COMPUTED: Self = Self(1 << 25);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl BitOr for NodeCheckFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for NodeCheckFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for NodeCheckFlags {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for NodeCheckFlags {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl Not for NodeCheckFlags {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

/// Exact state domain of `SignatureLinks.resolvedSignature`.
///
/// `Resolving` is the pinned checker's distinguished `resolvingSignature`;
/// no other signature-link field admits that recursion sentinel.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum ResolvedSignatureState {
    #[default]
    Unresolved,
    Resolving,
    Resolved(SignatureId),
}

impl ResolvedSignatureState {
    #[must_use]
    pub const fn signature(self) -> Option<SignatureId> {
        match self {
            Self::Resolved(signature) => Some(signature),
            Self::Unresolved | Self::Resolving => None,
        }
    }
}

/// Exact state domain of `SignatureLinks.effectsSignature`.
///
/// `NoEffects` represents the private `unknownSignature` sentinel returned to
/// callers as no control-flow effects.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum EffectsSignatureState {
    #[default]
    Unresolved,
    NoEffects,
    Resolved(SignatureId),
}

impl EffectsSignatureState {
    #[must_use]
    pub const fn signature(self) -> Option<SignatureId> {
        match self {
            Self::Resolved(signature) => Some(signature),
            Self::Unresolved | Self::NoEffects => None,
        }
    }
}

/// Exact state domain of `SignatureLinks.decoratorSignature`.
///
/// `NotApplicable` represents the private `anySignature` sentinel used to
/// cache a negative decorator-signature result.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum DecoratorSignatureState {
    #[default]
    Unresolved,
    NotApplicable,
    Resolved(SignatureId),
}

impl DecoratorSignatureState {
    #[must_use]
    pub const fn signature(self) -> Option<SignatureId> {
        match self {
            Self::Resolved(signature) => Some(signature),
            Self::Unresolved | Self::NotApplicable => None,
        }
    }
}

/// Exact state domain of `AliasSymbolLinks.aliasTarget`.
///
/// `Unknown` is the pinned checker's private `unknownSymbol` sentinel. Other
/// symbol caches retain that singleton as a concrete `SemanticSymbolId`; only
/// alias resolution interprets it as a cached negative result.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum AliasTargetState {
    #[default]
    Unresolved,
    Unknown,
    Resolved(SemanticSymbolId),
}

impl AliasTargetState {
    #[must_use]
    pub const fn symbol(self) -> Option<SemanticSymbolId> {
        match self {
            Self::Resolved(symbol) => Some(symbol),
            Self::Unresolved | Self::Unknown => None,
        }
    }

    #[must_use]
    pub const fn has_property(self) -> bool {
        !matches!(self, Self::Unresolved)
    }
}

/// Common links attached to syntax nodes.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NodeLinks {
    pub flags: NodeCheckFlags,
    pub declaration_requires_scope_change: Tristate,
    pub has_reported_statement_in_ambient_context: bool,
}

/// Cached symbol resolution for a syntax node.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolNodeLinks {
    pub resolved_symbol: Option<SemanticSymbolId>,
}

/// Cached type resolution for a syntax node.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeNodeLinks {
    pub resolved_type: Option<TypeId>,
    /// `None` is not computed/non-generic; `Some([])` is a computed empty set.
    pub outer_type_parameters: Option<Vec<TypeId>>,
}

/// Cached operand type for an assertion expression.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AssertionLinks {
    pub expr_type: Option<TypeId>,
}

/// Lazily computed spread bounds for an array literal.
///
/// The zero defaults are intentional. Upstream only assigns `-1` while
/// computing the indices; the default Go record is `(false, 0, 0)`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ArrayLiteralLinks {
    pub indices_computed: bool,
    pub first_spread_index: isize,
    pub last_spread_index: isize,
}

/// Exact lazy state domain of switch exhaustiveness.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum ExhaustiveState {
    #[default]
    Unknown = 0,
    Computing = 1,
    False = 2,
    True = 3,
}

/// Flow-analysis links attached to a switch statement.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SwitchStatementLinks {
    pub exhaustive_state: ExhaustiveState,
    pub switch_types_computed: bool,
    pub witnesses_computed: bool,
    /// `None` is nil; `Some([])` is an allocated empty slice.
    pub switch_types: Option<Vec<TypeId>>,
    /// `None` is nil; `Some([])` is an allocated empty slice.
    pub witnesses: Option<Vec<String>>,
}

/// JSX element classification flags from the pinned checker.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct JsxFlags(u32);

impl JsxFlags {
    pub const NONE: Self = Self(0);
    pub const INTRINSIC_NAMED_ELEMENT: Self = Self(1 << 0);
    pub const INTRINSIC_INDEXED_ELEMENT: Self = Self(1 << 1);
    pub const INTRINSIC_ELEMENT: Self =
        Self(Self::INTRINSIC_NAMED_ELEMENT.0 | Self::INTRINSIC_INDEXED_ELEMENT.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl BitOr for JsxFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for JsxFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// Checker caches attached to JSX elements and source-file JSX resolution.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct JsxElementLinks {
    pub jsx_flags: JsxFlags,
    pub resolved_jsx_element_attributes_type: Option<TypeId>,
    pub jsx_namespace: Option<SemanticSymbolId>,
    pub jsx_implicit_import_container: Option<SemanticSymbolId>,
}

/// Signature-specific syntax-node links.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SignatureLinks {
    pub resolved_signature: ResolvedSignatureState,
    pub effects_signature: EffectsSignatureState,
    pub decorator_signature: DecoratorSignatureState,
}

/// Reference meanings observed for one symbol.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolReferenceLinks {
    pub reference_kinds: SymbolFlags,
}

/// Type and mapper links attached to value symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ValueSymbolLinks {
    pub resolved_type: Option<TypeId>,
    pub write_type: Option<TypeId>,
    pub target: Option<SemanticSymbolId>,
    pub mapper: Option<TypeMapperId>,
    pub name_type: Option<TypeId>,
    pub containing_type: Option<TypeId>,
    pub function_or_constructor_checked: bool,
}

/// Additional links for mapped symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MappedSymbolLinks {
    pub key_type: Option<TypeId>,
    pub synthetic_origin: Option<SemanticSymbolId>,
}

/// Additional links for deferred union/intersection symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DeferredSymbolLinks {
    pub parent: Option<TypeId>,
    /// `None` is not computed; `Some([])` is a computed empty slice.
    pub constituents: Option<Vec<TypeId>>,
    /// `None` is not computed; `Some([])` is a computed empty slice.
    pub write_constituents: Option<Vec<TypeId>>,
}

/// Alias-target and use-state links.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AliasSymbolLinks {
    pub immediate_target: Option<SemanticSymbolId>,
    pub alias_target: AliasTargetState,
    pub referenced: bool,
    pub type_only_declaration: Option<NodeRef>,
}

/// Module export-resolution links.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModuleSymbolLinks {
    /// `None` is a nil symbol table; an allocated empty table remains a
    /// concrete `SymbolTableId`.
    pub resolved_exports: Option<super::SymbolTableId>,
    /// `None` is a nil map; `Some({})` is an allocated empty map.
    pub type_only_export_star_map: Option<HashMap<EscapedName, Option<NodeRef>>>,
    pub exports_checked: bool,
}

/// Links for a symbol produced by late binding.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LateBoundLinks {
    pub late_symbol: Option<SemanticSymbolId>,
}

/// Target and diagnostic origin for a synthetic export-type symbol.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ExportTypeLinks {
    pub target: Option<SemanticSymbolId>,
    pub originating_import: Option<NodeRef>,
}

/// Links specific to type-alias symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeAliasLinks {
    pub declared_type: Option<TypeId>,
    /// `None` is a non-generic alias; `Some([])` remains observably allocated.
    pub type_parameters: Option<Vec<TypeId>>,
    /// `None` is unallocated; `Some({})` is an allocated empty cache.
    pub instantiations: Option<HashMap<CacheHashKey, TypeId>>,
    pub is_constructor_declared_property: bool,
}

/// Links shared by declared types (type parameters, classes, interfaces, and
/// enums).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)] // Mirrors the complete upstream link record.
pub struct DeclaredTypeLinks {
    pub declared_type: Option<TypeId>,
    pub interface_checked: bool,
    pub index_signatures_checked: bool,
    pub type_parameters_checked: bool,
    pub enum_checked: bool,
}

/// Selector used to index [`MembersAndExportsLinks`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(usize)]
pub enum MembersOrExportsResolutionKind {
    ResolvedExports = 0,
    ResolvedMembers = 1,
}

/// Separate cached tables for resolved exports and resolved members.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MembersAndExportsLinks {
    pub tables: [Option<super::SymbolTableId>; 2],
}

impl MembersAndExportsLinks {
    #[must_use]
    pub const fn table(
        &self,
        kind: MembersOrExportsResolutionKind,
    ) -> Option<super::SymbolTableId> {
        self.tables[kind as usize]
    }
}

/// Source symbols for a synthetic spread property.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SpreadLinks {
    pub left_spread: Option<SemanticSymbolId>,
    pub right_spread: Option<SemanticSymbolId>,
}

/// Cached variances for a type alias or interface symbol.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VarianceLinks {
    /// `None` is not computed; `Some([])` is a computed empty slice.
    pub variances: Option<Vec<VarianceFlags>>,
}

/// Reverse-mapped property type inputs.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ReverseMappedSymbolLinks {
    pub property_type: Option<TypeId>,
    pub mapped_type: Option<TypeId>,
    pub constraint_type: Option<TypeId>,
}

/// Assignment-marking state for a symbol.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MarkedAssignmentSymbolLinks {
    pub last_assignment_pos: i32,
    pub has_definite_assignment: bool,
}

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct LinkStoreId(NonZeroU64);

impl std::fmt::Debug for LinkStoreId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("LinkStoreId")
    }
}

static LAST_LINK_STORE_ID: AtomicU64 = AtomicU64::new(0);

fn allocate_link_store_id() -> LinkStoreId {
    let previous = LAST_LINK_STORE_ID
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .unwrap_or_else(|_| panic!("link store identity space exhausted"));
    LinkStoreId(NonZeroU64::new(previous + 1).expect("successful allocation is nonzero"))
}

/// Stable logical identity of one sparse link record.
///
/// Handles are branded by their originating store.  A handle remains valid as
/// the backing map and arena grow, and cannot alias the same slot number in a
/// different `LinkStore`.
pub struct LinkHandle<V> {
    store: LinkStoreId,
    slot: usize,
    value: PhantomData<fn() -> V>,
}

impl<V> Clone for LinkHandle<V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<V> Copy for LinkHandle<V> {}

impl<V> std::fmt::Debug for LinkHandle<V> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LinkHandle")
            .field("store", &self.store)
            .field("slot", &self.slot)
            .finish()
    }
}

impl<V> PartialEq for LinkHandle<V> {
    fn eq(&self, other: &Self) -> bool {
        self.store == other.store && self.slot == other.slot
    }
}

impl<V> Eq for LinkHandle<V> {}

impl<V> Hash for LinkHandle<V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.store.hash(state);
        self.slot.hash(state);
    }
}

/// Sparse, arena-backed link storage matching `internal/core/linkstore.go`.
///
/// `get` allocates exactly one default record per new key. `has` and
/// `try_get` never allocate. There is intentionally no delete or iteration
/// API. Mutation is replacement by stable handle, which lets callers snapshot
/// state, install a recursion sentinel, recurse after the borrow ends, and
/// finally refetch/commit.
#[derive(Debug)]
pub struct LinkStore<K, V> {
    id: LinkStoreId,
    entries: HashMap<K, usize>,
    arena: Vec<V>,
}

impl<K, V> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self {
            id: allocate_link_store_id(),
            entries: HashMap::new(),
            arena: Vec::new(),
        }
    }
}

impl<K: Eq + Hash, V: Default> LinkStore<K, V> {
    /// Returns the stable handle for `key`, allocating one default record if
    /// and only if the key was absent.
    pub fn get(&mut self, key: K) -> LinkHandle<V> {
        if let Some(slot) = self.entries.get(&key).copied() {
            return self.handle(slot);
        }
        let slot = self.arena.len();
        self.arena.push(V::default());
        self.entries.insert(key, slot);
        self.handle(slot)
    }
}

impl<K: Eq + Hash, V> LinkStore<K, V> {
    /// Tests allocation state without allocating a record.
    #[must_use]
    pub fn has(&self, key: &K) -> bool {
        self.entries.contains_key(key)
    }

    /// Reads an allocated record without allocating on a miss.
    #[must_use]
    pub fn try_get(&self, key: &K) -> Option<&V> {
        let slot = self.entries.get(key).copied()?;
        self.arena.get(slot)
    }

    /// Reads a record through a stable handle. Foreign handles are rejected.
    #[must_use]
    pub fn value(&self, handle: LinkHandle<V>) -> Option<&V> {
        (handle.store == self.id)
            .then(|| self.arena.get(handle.slot))
            .flatten()
    }

    /// Replaces a record through a stable handle. Foreign handles are
    /// rejected without mutation.
    pub fn replace(&mut self, handle: LinkHandle<V>, value: V) -> bool {
        if handle.store != self.id {
            return false;
        }
        let Some(slot) = self.arena.get_mut(handle.slot) else {
            return false;
        };
        *slot = value;
        true
    }

    pub(super) fn replace_key(&mut self, key: K, value: V) -> LinkHandle<V>
    where
        V: Default,
    {
        let handle = self.get(key);
        let replaced = self.replace(handle, value);
        debug_assert!(replaced, "fresh same-store link handle must be valid");
        handle
    }

    fn handle(&self, slot: usize) -> LinkHandle<V> {
        LinkHandle {
            store: self.id,
            slot,
            value: PhantomData,
        }
    }

    pub(super) fn allocated_len(&self) -> usize {
        self.arena.len()
    }
}

/// Typed target of one lazy type-system property resolution.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TypeResolutionTarget {
    Symbol(SemanticSymbolId),
    Type(TypeId),
    Signature(SignatureId),
    Node(NodeRef),
}

/// Property names and numeric ordering from typescript-go's
/// `TypeSystemPropertyName`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(i32)]
pub enum TypeSystemPropertyName {
    Type = 0,
    ResolvedBaseConstructorType = 1,
    DeclaredType = 2,
    ResolvedReturnType = 3,
    ResolvedBaseConstraint = 4,
    ResolvedTypeArguments = 5,
    ResolvedBaseTypes = 6,
    WriteType = 7,
    InitializerIsUndefined = 8,
    AliasTarget = 9,
}

impl TypeSystemPropertyName {
    #[must_use]
    pub const fn accepts(self, target: TypeResolutionTarget) -> bool {
        matches!(
            (self, target),
            (
                Self::Type | Self::DeclaredType | Self::WriteType | Self::AliasTarget,
                TypeResolutionTarget::Symbol(_)
            ) | (
                Self::ResolvedBaseConstructorType
                    | Self::ResolvedBaseConstraint
                    | Self::ResolvedTypeArguments
                    | Self::ResolvedBaseTypes,
                TypeResolutionTarget::Type(_)
            ) | (Self::ResolvedReturnType, TypeResolutionTarget::Signature(_))
                | (Self::InitializerIsUndefined, TypeResolutionTarget::Node(_))
        )
    }
}

/// Invalid target/property pairing supplied to the typed resolution stack.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TypeResolutionTargetError {
    pub target: TypeResolutionTarget,
    pub property: TypeSystemPropertyName,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TypeResolution {
    target: TypeResolutionTarget,
    property: TypeSystemPropertyName,
    result: bool,
}

/// Opaque restoration token for a temporary type-resolution boundary.
///
/// Tokens are store-branded, single-use, and must be restored in LIFO order.
/// Safe callers cannot construct or duplicate one.
#[derive(Debug)]
#[must_use = "resolution boundaries must be restored in LIFO order"]
pub struct TypeResolutionBoundary {
    owner: SemanticStoreId,
    serial: u64,
}

#[derive(Debug)]
struct TypeResolutionBoundaryFrame {
    serial: u64,
    previous_start: usize,
    boundary_depth: usize,
}

/// Cycle-detection stack for lazy type-system property resolution.
#[derive(Debug)]
pub(super) struct TypeResolutionStack {
    owner: SemanticStoreId,
    entries: Vec<TypeResolution>,
    resolution_start: usize,
    boundaries: Vec<TypeResolutionBoundaryFrame>,
    next_boundary_serial: u64,
}

impl TypeResolutionStack {
    pub(super) const fn new(owner: SemanticStoreId) -> Self {
        Self {
            owner,
            entries: Vec::new(),
            resolution_start: 0,
            boundaries: Vec::new(),
            next_boundary_serial: 0,
        }
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(super) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub(super) const fn resolution_start(&self) -> usize {
        self.resolution_start
    }

    #[must_use]
    pub(super) fn boundary_len(&self) -> usize {
        self.boundaries.len()
    }

    #[must_use]
    pub(super) const fn next_boundary_serial(&self) -> u64 {
        self.next_boundary_serial
    }

    /// Temporarily starts cycle scanning at the current stack depth.
    ///
    /// # Panics
    ///
    /// Panics before mutation if this stack exhausts its boundary-token
    /// identity space.
    pub(super) fn reset_resolution_start(&mut self) -> TypeResolutionBoundary {
        let serial = self
            .next_boundary_serial
            .checked_add(1)
            .expect("type resolution boundary identity space exhausted");
        let previous_start = self.resolution_start;
        self.next_boundary_serial = serial;
        self.boundaries.push(TypeResolutionBoundaryFrame {
            serial,
            previous_start,
            boundary_depth: self.entries.len(),
        });
        self.resolution_start = self.entries.len();
        TypeResolutionBoundary {
            owner: self.owner,
            serial,
        }
    }

    /// Restores the most recent boundary. Foreign, reused, out-of-order, or
    /// still-active tokens are returned to the caller without mutation.
    pub(super) fn restore_resolution_start(
        &mut self,
        token: TypeResolutionBoundary,
    ) -> Result<(), TypeResolutionBoundary> {
        let Some(frame) = self.boundaries.last() else {
            return Err(token);
        };
        if token.owner != self.owner
            || token.serial != frame.serial
            || self.entries.len() != frame.boundary_depth
        {
            return Err(token);
        }
        let frame = self
            .boundaries
            .pop()
            .expect("validated boundary frame exists");
        self.resolution_start = frame.previous_start;
        Ok(())
    }

    /// Ports `pushTypeResolution`.
    ///
    /// `has_property` probes disjoint live semantic fields while this stack is
    /// borrowed. A found cycle marks the existing entry and every later entry
    /// false and does not push a new entry.
    pub(super) fn push(
        &mut self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
        mut has_property: impl FnMut(TypeResolutionTarget, TypeSystemPropertyName) -> bool,
    ) -> Result<bool, TypeResolutionTargetError> {
        Self::validate_target(target, property)?;
        if let Some(start) = self.find_cycle_start_index_inner(target, property, &mut has_property)
        {
            for resolution in &mut self.entries[start..] {
                resolution.result = false;
            }
            return Ok(false);
        }
        self.entries.push(TypeResolution {
            target,
            property,
            result: true,
        });
        Ok(true)
    }

    /// Ports `popTypeResolution`. Empty stacks return `None` instead of
    /// reproducing an upstream out-of-bounds panic. An active boundary also
    /// prevents callers from popping an entry owned by its outer scope.
    pub(super) fn pop(&mut self) -> Option<bool> {
        if self
            .boundaries
            .last()
            .is_some_and(|boundary| self.entries.len() <= boundary.boundary_depth)
        {
            return None;
        }
        Some(self.entries.pop()?.result)
    }

    /// Ports `findResolutionCycleStartIndex`, returning `None` for upstream's
    /// `-1` result.
    pub(super) fn find_cycle_start_index(
        &self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
        mut has_property: impl FnMut(TypeResolutionTarget, TypeSystemPropertyName) -> bool,
    ) -> Result<Option<usize>, TypeResolutionTargetError> {
        Self::validate_target(target, property)?;
        Ok(self.find_cycle_start_index_inner(target, property, &mut has_property))
    }

    fn find_cycle_start_index_inner(
        &self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
        has_property: &mut impl FnMut(TypeResolutionTarget, TypeSystemPropertyName) -> bool,
    ) -> Option<usize> {
        for index in (self.resolution_start..self.entries.len()).rev() {
            let resolution = self.entries[index];
            if has_property(resolution.target, resolution.property) {
                return None;
            }
            if resolution.target == target && resolution.property == property {
                return Some(index);
            }
        }
        None
    }

    fn validate_target(
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) -> Result<(), TypeResolutionTargetError> {
        if property.accepts(target) {
            Ok(())
        } else {
            Err(TypeResolutionTargetError { target, property })
        }
    }
}

/// The dependency-closed typed checker link stores.
#[derive(Debug, Default)]
pub(super) struct CheckerLinkStores {
    pub(super) node: LinkStore<NodeRef, NodeLinks>,
    pub(super) symbol_node: LinkStore<NodeRef, SymbolNodeLinks>,
    pub(super) type_node: LinkStore<NodeRef, TypeNodeLinks>,
    pub(super) assertion: LinkStore<NodeRef, AssertionLinks>,
    pub(super) array_literal: LinkStore<NodeRef, ArrayLiteralLinks>,
    pub(super) switch_statement: LinkStore<NodeRef, SwitchStatementLinks>,
    pub(super) jsx_element: LinkStore<NodeRef, JsxElementLinks>,
    pub(super) signature: LinkStore<NodeRef, SignatureLinks>,
    pub(super) symbol_reference: LinkStore<SemanticSymbolId, SymbolReferenceLinks>,
    pub(super) value_symbol: LinkStore<SemanticSymbolId, ValueSymbolLinks>,
    pub(super) mapped_symbol: LinkStore<SemanticSymbolId, MappedSymbolLinks>,
    pub(super) deferred_symbol: LinkStore<SemanticSymbolId, DeferredSymbolLinks>,
    pub(super) alias_symbol: LinkStore<SemanticSymbolId, AliasSymbolLinks>,
    pub(super) module_symbol: LinkStore<SemanticSymbolId, ModuleSymbolLinks>,
    pub(super) late_bound: LinkStore<SemanticSymbolId, LateBoundLinks>,
    pub(super) export_type: LinkStore<SemanticSymbolId, ExportTypeLinks>,
    pub(super) members_and_exports: LinkStore<SemanticSymbolId, MembersAndExportsLinks>,
    pub(super) type_alias: LinkStore<SemanticSymbolId, TypeAliasLinks>,
    pub(super) declared_type: LinkStore<SemanticSymbolId, DeclaredTypeLinks>,
    pub(super) spread: LinkStore<SemanticSymbolId, SpreadLinks>,
    pub(super) variance: LinkStore<SemanticSymbolId, VarianceLinks>,
    pub(super) reverse_mapped_symbol: LinkStore<SemanticSymbolId, ReverseMappedSymbolLinks>,
    pub(super) marked_assignment_symbol: LinkStore<SemanticSymbolId, MarkedAssignmentSymbolLinks>,
}

impl CheckerLinkStores {
    #[must_use]
    pub(super) fn allocated_lengths(&self) -> [usize; 23] {
        [
            self.node.allocated_len(),
            self.symbol_node.allocated_len(),
            self.type_node.allocated_len(),
            self.assertion.allocated_len(),
            self.array_literal.allocated_len(),
            self.switch_statement.allocated_len(),
            self.jsx_element.allocated_len(),
            self.signature.allocated_len(),
            self.symbol_reference.allocated_len(),
            self.value_symbol.allocated_len(),
            self.mapped_symbol.allocated_len(),
            self.deferred_symbol.allocated_len(),
            self.alias_symbol.allocated_len(),
            self.module_symbol.allocated_len(),
            self.late_bound.allocated_len(),
            self.export_type.allocated_len(),
            self.members_and_exports.allocated_len(),
            self.type_alias.allocated_len(),
            self.declared_type.allocated_len(),
            self.spread.allocated_len(),
            self.variance.allocated_len(),
            self.reverse_mapped_symbol.allocated_len(),
            self.marked_assignment_symbol.allocated_len(),
        ]
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_binder::SymbolFlags;

    use super::{
        AliasTargetState, ArrayLiteralLinks, CacheHashKey, DecoratorSignatureState,
        DeferredSymbolLinks, EffectsSignatureState, ExhaustiveState, JsxFlags, LinkStore,
        MembersAndExportsLinks, MembersOrExportsResolutionKind, ModuleSymbolLinks, NodeCheckFlags,
        ResolvedSignatureState, SwitchStatementLinks, Tristate, TypeAliasLinks,
        TypeResolutionStack, TypeResolutionTarget, TypeSystemPropertyName, VarianceFlags,
        VarianceLinks,
    };

    #[test]
    fn generic_link_store_preserves_sparse_allocation_and_stable_identity() {
        let mut links = LinkStore::<u32, Vec<u32>>::default();

        assert!(!links.has(&7));
        assert_eq!(links.try_get(&7), None);
        assert_eq!(links.allocated_len(), 0);

        let first = links.get(7);
        assert!(links.has(&7));
        assert_eq!(links.try_get(&7), Some(&Vec::new()));
        assert_eq!(links.allocated_len(), 1);

        for key in 0..256 {
            let _ = links.get(key);
        }
        let again = links.get(7);
        assert_eq!(first, again);
        assert_eq!(links.value(first), Some(&Vec::new()));
        assert!(links.replace(first, vec![1, 2, 3]));
        assert_eq!(links.try_get(&7), Some(&vec![1, 2, 3]));
        assert_eq!(links.get(7), first);
    }

    #[test]
    fn link_handles_are_store_branded() {
        let mut first = LinkStore::<u32, u32>::default();
        let mut second = LinkStore::<u32, u32>::default();
        let first_handle = first.get(1);
        let second_handle = second.get(1);

        assert_ne!(first_handle, second_handle);
        assert_eq!(first.value(second_handle), None);
        assert!(!first.replace(second_handle, 9));
        assert_eq!(first.value(first_handle), Some(&0));
    }

    #[test]
    fn exact_node_check_flag_values_are_preserved() {
        let flags = [
            (NodeCheckFlags::NONE, 0),
            (NodeCheckFlags::TYPE_CHECKED, 1 << 0),
            (NodeCheckFlags::CONTEXT_CHECKED, 1 << 6),
            (NodeCheckFlags::ENUM_VALUES_COMPUTED, 1 << 10),
            (NodeCheckFlags::ASSIGNMENTS_MARKED, 1 << 17),
            (
                NodeCheckFlags::CONTAINS_CLASS_WITH_PRIVATE_IDENTIFIERS,
                1 << 20,
            ),
            (
                NodeCheckFlags::CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER,
                1 << 21,
            ),
            (NodeCheckFlags::IN_CHECK_IDENTIFIER, 1 << 22),
            (NodeCheckFlags::INITIALIZER_IS_UNDEFINED, 1 << 24),
            (NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED, 1 << 25),
        ];
        for (flag, expected) in flags {
            assert_eq!(flag.bits(), expected);
        }

        let combined = NodeCheckFlags::TYPE_CHECKED | NodeCheckFlags::CONTEXT_CHECKED;
        assert!(combined.contains(NodeCheckFlags::TYPE_CHECKED));
        assert!(combined.intersects(NodeCheckFlags::CONTEXT_CHECKED));
        assert_eq!((combined & !NodeCheckFlags::TYPE_CHECKED).bits(), 1 << 6);
    }

    #[test]
    fn sparse_link_enums_and_flags_preserve_exact_numeric_values() {
        assert_eq!(ExhaustiveState::Unknown as u8, 0);
        assert_eq!(ExhaustiveState::Computing as u8, 1);
        assert_eq!(ExhaustiveState::False as u8, 2);
        assert_eq!(ExhaustiveState::True as u8, 3);

        assert_eq!(JsxFlags::NONE.bits(), 0);
        assert_eq!(JsxFlags::INTRINSIC_NAMED_ELEMENT.bits(), 1);
        assert_eq!(JsxFlags::INTRINSIC_INDEXED_ELEMENT.bits(), 2);
        assert_eq!(JsxFlags::INTRINSIC_ELEMENT.bits(), 3);

        assert_eq!(VarianceFlags::INVARIANT.bits(), 0);
        assert_eq!(VarianceFlags::COVARIANT.bits(), 1);
        assert_eq!(VarianceFlags::CONTRAVARIANT.bits(), 2);
        assert_eq!(VarianceFlags::BIVARIANT.bits(), 3);
        assert_eq!(VarianceFlags::INDEPENDENT.bits(), 4);
        assert_eq!(VarianceFlags::VARIANCE_MASK.bits(), 7);
        assert_eq!(VarianceFlags::UNMEASURABLE.bits(), 8);
        assert_eq!(VarianceFlags::UNRELIABLE.bits(), 16);
        assert_eq!(VarianceFlags::ALLOWS_STRUCTURAL_FALLBACK.bits(), 24);

        assert_eq!(MembersOrExportsResolutionKind::ResolvedExports as usize, 0);
        assert_eq!(MembersOrExportsResolutionKind::ResolvedMembers as usize, 1);
    }

    #[test]
    fn new_sparse_links_preserve_pinned_defaults_and_allocated_empty_states() {
        assert_eq!(
            ArrayLiteralLinks::default(),
            ArrayLiteralLinks {
                indices_computed: false,
                first_spread_index: 0,
                last_spread_index: 0,
            }
        );
        assert_eq!(
            SwitchStatementLinks::default().exhaustive_state,
            ExhaustiveState::Unknown
        );

        let computed_empty_switch = SwitchStatementLinks {
            switch_types: Some(Vec::new()),
            witnesses: Some(Vec::new()),
            ..SwitchStatementLinks::default()
        };
        assert_ne!(computed_empty_switch, SwitchStatementLinks::default());

        let computed_empty_deferred = DeferredSymbolLinks {
            constituents: Some(Vec::new()),
            write_constituents: Some(Vec::new()),
            ..DeferredSymbolLinks::default()
        };
        assert_ne!(computed_empty_deferred, DeferredSymbolLinks::default());

        let computed_empty_variance = VarianceLinks {
            variances: Some(Vec::new()),
        };
        assert_ne!(computed_empty_variance, VarianceLinks::default());
        let allocated_empty_module_map = ModuleSymbolLinks {
            type_only_export_star_map: Some(HashMap::new()),
            ..ModuleSymbolLinks::default()
        };
        assert_ne!(allocated_empty_module_map, ModuleSymbolLinks::default());
        assert_eq!(MembersAndExportsLinks::default().tables, [None, None]);
    }

    #[test]
    fn tristate_matches_upstream_values_and_predicates() {
        assert_eq!(Tristate::Unknown as u8, 0);
        assert_eq!(Tristate::False as u8, 1);
        assert_eq!(Tristate::True as u8, 2);
        assert!(Tristate::Unknown.is_unknown());
        assert!(Tristate::Unknown.is_true_or_unknown());
        assert!(Tristate::Unknown.is_false_or_unknown());
        assert!(Tristate::False.is_false());
        assert!(Tristate::True.is_true());
        assert_eq!(
            Tristate::Unknown.default_if_unknown(Tristate::True),
            Tristate::True
        );
        assert_eq!(
            Tristate::False.default_if_unknown(Tristate::True),
            Tristate::False
        );
        assert_eq!(Tristate::from(false), Tristate::False);
        assert_eq!(Tristate::from(true), Tristate::True);
    }

    #[test]
    fn exact_field_states_and_allocated_empty_collections_remain_distinct() {
        assert_ne!(
            ResolvedSignatureState::Unresolved,
            ResolvedSignatureState::Resolving
        );
        assert_ne!(
            EffectsSignatureState::Unresolved,
            EffectsSignatureState::NoEffects
        );
        assert_ne!(
            DecoratorSignatureState::Unresolved,
            DecoratorSignatureState::NotApplicable
        );
        assert_eq!(ResolvedSignatureState::Resolving.signature(), None);
        assert_eq!(EffectsSignatureState::NoEffects.signature(), None);
        assert_eq!(DecoratorSignatureState::NotApplicable.signature(), None);
        assert!(!AliasTargetState::Unresolved.has_property());
        assert!(AliasTargetState::Unknown.has_property());
        assert_eq!(AliasTargetState::Unknown.symbol(), None);

        let unallocated = TypeAliasLinks::default();
        let allocated_empty = TypeAliasLinks {
            type_parameters: Some(Vec::new()),
            instantiations: Some(HashMap::new()),
            ..TypeAliasLinks::default()
        };
        assert_ne!(unallocated, allocated_empty);
    }

    #[test]
    fn cache_hash_key_preserves_both_halves_and_zero_state() {
        assert!(CacheHashKey::default().is_zero());
        let key = CacheHashKey::from_halves(0xfedc_ba98_7654_3210, 0x0123_4567_89ab_cdef);
        assert_eq!(
            key.get(),
            (u128::from(0xfedc_ba98_7654_3210_u64) << 64) | u128::from(0x0123_4567_89ab_cdef_u64)
        );
        assert!(!key.is_zero());
    }

    #[test]
    fn property_numbers_and_target_kinds_are_exact() {
        use TypeSystemPropertyName as Property;

        assert_eq!(Property::Type as i32, 0);
        assert_eq!(Property::ResolvedBaseConstructorType as i32, 1);
        assert_eq!(Property::DeclaredType as i32, 2);
        assert_eq!(Property::ResolvedReturnType as i32, 3);
        assert_eq!(Property::ResolvedBaseConstraint as i32, 4);
        assert_eq!(Property::ResolvedTypeArguments as i32, 5);
        assert_eq!(Property::ResolvedBaseTypes as i32, 6);
        assert_eq!(Property::WriteType as i32, 7);
        assert_eq!(Property::InitializerIsUndefined as i32, 8);
        assert_eq!(Property::AliasTarget as i32, 9);
    }

    #[test]
    fn resolution_stack_marks_cycles_and_does_not_push_duplicate() {
        let (owner, symbol, other) = test_symbol_targets();
        let mut stack = TypeResolutionStack::new(owner);

        assert_eq!(
            stack.push(symbol, TypeSystemPropertyName::Type, |_, _| false),
            Ok(true)
        );
        assert_eq!(
            stack.push(other, TypeSystemPropertyName::Type, |_, _| false),
            Ok(true)
        );
        assert_eq!(
            stack.push(symbol, TypeSystemPropertyName::Type, |_, _| false),
            Ok(false)
        );
        assert_eq!(stack.len(), 2);
        assert_eq!(stack.pop(), Some(false));
        assert_eq!(stack.pop(), Some(false));
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn resolved_property_and_resolution_boundary_break_cycle_scan() {
        let (owner, symbol, other) = test_symbol_targets();
        let mut stack = TypeResolutionStack::new(owner);
        stack
            .push(symbol, TypeSystemPropertyName::Type, |_, _| false)
            .unwrap();
        stack
            .push(other, TypeSystemPropertyName::Type, |_, _| false)
            .unwrap();

        let no_cycle = stack
            .find_cycle_start_index(symbol, TypeSystemPropertyName::Type, |target, _| {
                target == other
            })
            .unwrap();
        assert_eq!(no_cycle, None);

        let boundary = stack.reset_resolution_start();
        assert_eq!(stack.resolution_start(), 2);
        assert!(
            stack
                .push(symbol, TypeSystemPropertyName::Type, |_, _| false)
                .unwrap()
        );
        let boundary = stack
            .restore_resolution_start(boundary)
            .expect_err("a live entry inside the boundary prevents restoration");
        assert_eq!(stack.resolution_start(), 2);
        assert_eq!(stack.pop(), Some(true));
        assert!(stack.restore_resolution_start(boundary).is_ok());
        assert_eq!(stack.pop(), Some(true));
        assert_eq!(stack.pop(), Some(true));
    }

    #[test]
    fn resolution_stack_rejects_wrong_target_kind_without_mutation() {
        let (owner, symbol, _) = test_symbol_targets();
        let mut stack = TypeResolutionStack::new(owner);
        let error = stack
            .push(
                symbol,
                TypeSystemPropertyName::ResolvedReturnType,
                |_, _| false,
            )
            .unwrap_err();
        assert_eq!(error.target, symbol);
        assert_eq!(error.property, TypeSystemPropertyName::ResolvedReturnType);
        assert!(stack.is_empty());
    }

    fn test_symbol_targets() -> (
        ts_binder::SemanticStoreId,
        TypeResolutionTarget,
        TypeResolutionTarget,
    ) {
        let mut store = ts_binder::SymbolStore::new();
        let owner = store.id();
        let first = store.alloc_transient_symbol(
            SymbolFlags::TRANSIENT,
            ts_binder::EscapedName::source("first"),
            ts_binder::CheckFlags::NONE,
        );
        let second = store.alloc_transient_symbol(
            SymbolFlags::TRANSIENT,
            ts_binder::EscapedName::source("second"),
            ts_binder::CheckFlags::NONE,
        );
        (
            owner,
            TypeResolutionTarget::Symbol(first),
            TypeResolutionTarget::Symbol(second),
        )
    }
}
