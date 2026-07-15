//! Exact dependency-closed `NewChecker` intrinsic bootstrap.
//!
//! This module is pinned to `internal/checker/checker.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`, from the checker-owned symbols
//! through `typeofType` (approximately lines 953-1050). It deliberately stops
//! at semantic boundaries that the canonical graph cannot yet represent:
//!
//! - `uniqueLiteralMapper`, the report mappers, and the restrictive/permissive
//!   mappers own executable Go callbacks. [`TypeMapper`] intentionally has no
//!   callback-shaped variant, so those five fields and their APIs remain absent.
//! - name resolvers, file-global merges, global-library lookup, relation-key
//!   construction and relation algorithms, flow caches, and
//!   `initializeChecker` depend on Program/host behavior. The relation cache
//!   owners exist as exact empty state, but no relation result is fabricated.
//!   The empty globals table and `globalThis` insertion performed by
//!   `NewChecker` itself are included; resolving or augmenting that table is
//!   not.
//! - general literal, union, and template-literal reduction algorithms remain
//!   outside this module. The closed bootstrap cases below encode their pinned
//!   normalized results and seed the exact cache entries produced by upstream,
//!   without exposing an approximate general reduction API.

use std::collections::HashMap;

use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    ids::{IndexInfoId, SignatureId, TypeId, TypePredicateId},
    mapper::TypeMapper,
    relation::RelationStateSnapshot,
    signatures::{SignatureFlags, TypePredicateKind},
    store::SemanticStore,
    type_records::{LiteralValue, RegularLiteralLink, TypeCacheState, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// The two compiler options that alter pinned intrinsic bootstrap identity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct IntrinsicBootstrapOptions {
    pub strict_null_checks: bool,
    pub exact_optional_property_types: bool,
}

/// Arena counts captured before a rejected bootstrap attempt.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SemanticArenaCounts {
    pub types: usize,
    pub mappers: usize,
    pub signatures: usize,
    pub predicates: usize,
    pub index_infos: usize,
    pub type_aliases: usize,
    pub conditional_roots: usize,
    pub entity_names: usize,
}

impl SemanticArenaCounts {
    const fn is_empty(self) -> bool {
        self.types == 0
            && self.mappers == 0
            && self.signatures == 0
            && self.predicates == 0
            && self.index_infos == 0
            && self.type_aliases == 0
            && self.conditional_roots == 0
            && self.entity_names == 0
    }
}

/// Allocated record counts for the canonical sparse checker link stores.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckerLinkCounts {
    pub node: usize,
    pub symbol_node: usize,
    pub type_node: usize,
    pub enum_member: usize,
    pub assertion: usize,
    pub array_literal: usize,
    pub switch_statement: usize,
    pub jsx_element: usize,
    pub signature: usize,
    pub symbol_reference: usize,
    pub value_symbol: usize,
    pub mapped_symbol: usize,
    pub deferred_symbol: usize,
    pub alias_symbol: usize,
    pub module_symbol: usize,
    pub late_bound: usize,
    pub export_type: usize,
    pub members_and_exports: usize,
    pub type_alias: usize,
    pub declared_type: usize,
    pub spread: usize,
    pub variance: usize,
    pub reverse_mapped_symbol: usize,
    pub marked_assignment_symbol: usize,
    pub containing_symbol: usize,
    pub source_file: usize,
}

impl CheckerLinkCounts {
    const fn is_empty(self) -> bool {
        self.node == 0
            && self.symbol_node == 0
            && self.type_node == 0
            && self.enum_member == 0
            && self.assertion == 0
            && self.array_literal == 0
            && self.switch_statement == 0
            && self.jsx_element == 0
            && self.signature == 0
            && self.symbol_reference == 0
            && self.value_symbol == 0
            && self.mapped_symbol == 0
            && self.deferred_symbol == 0
            && self.alias_symbol == 0
            && self.module_symbol == 0
            && self.late_bound == 0
            && self.export_type == 0
            && self.members_and_exports == 0
            && self.type_alias == 0
            && self.declared_type == 0
            && self.spread == 0
            && self.variance == 0
            && self.reverse_mapped_symbol == 0
            && self.marked_assignment_symbol == 0
            && self.containing_symbol == 0
            && self.source_file == 0
    }
}

/// Observable and fail-closed history of the type-resolution stack.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TypeResolutionStateSnapshot {
    pub entries: usize,
    pub resolution_start: usize,
    pub boundaries: usize,
    pub next_boundary_serial: u64,
}

impl TypeResolutionStateSnapshot {
    const fn is_pristine(self) -> bool {
        self.entries == 0
            && self.resolution_start == 0
            && self.boundaries == 0
            && self.next_boundary_serial == 0
    }
}

/// All checker-owned state that must be pristine before `NewChecker` bootstrap.
///
/// Binder-owned symbols/tables, their lazy global IDs, and registered AST
/// scopes may predate checker construction. Checker-transient symbols are
/// counted separately and therefore fail closed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckerStateSnapshot {
    pub checker_symbols: usize,
    pub merged_symbols: usize,
    pub semantic_arenas: SemanticArenaCounts,
    pub links: CheckerLinkCounts,
    pub type_resolution: TypeResolutionStateSnapshot,
    pub relations: RelationStateSnapshot,
}

impl CheckerStateSnapshot {
    const fn is_pristine(self) -> bool {
        self.checker_symbols == 0
            && self.merged_symbols == 0
            && self.semantic_arenas.is_empty()
            && self.links.is_empty()
            && self.type_resolution.is_pristine()
            && self.relations.is_pristine()
    }
}

/// A bootstrap request rejected before any semantic allocation is performed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IntrinsicBootstrapError {
    /// The store already owns the singleton set under different compiler options.
    OptionsMismatch {
        initialized: IntrinsicBootstrapOptions,
        requested: IntrinsicBootstrapOptions,
    },
    /// `NewChecker` bootstrap must precede every checker-owned write.
    NonPristineCheckerState(Box<CheckerStateSnapshot>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct NumberLiteralCacheKey(u64);

impl NumberLiteralCacheKey {
    fn from_number(value: Number) -> Option<Self> {
        if value.is_nan() {
            return None;
        }
        let value = value.value();
        // Go map equality treats -0 and +0 as the same key. NaN has a separate
        // upstream slot and is never populated by NewChecker bootstrap.
        Some(Self(if value == 0.0 { 0 } else { value.to_bits() }))
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TemplateLiteralCacheKey {
    texts: Vec<String>,
    types: Vec<TypeId>,
}

/// Store-owned identities initialized by pinned `NewChecker`.
///
/// Fields are IDs rather than cloned semantic records. Distinct fields remain
/// distinct even when their flags and names match; option-controlled upstream
/// pointer aliases remain equal IDs.
#[derive(Debug, Eq, PartialEq)]
pub struct IntrinsicBootstrap {
    pub options: IntrinsicBootstrapOptions,

    pub globals: SymbolTableId,
    pub undefined_symbol: SemanticSymbolId,
    pub arguments_symbol: SemanticSymbolId,
    pub require_symbol: SemanticSymbolId,
    pub unknown_symbol: SemanticSymbolId,
    pub global_this_symbol: SemanticSymbolId,

    pub any_type: TypeId,
    pub auto_type: TypeId,
    pub wildcard_type: TypeId,
    pub blocked_string_type: TypeId,
    pub error_type: TypeId,
    pub unresolved_type: TypeId,
    pub non_inferrable_any_type: TypeId,
    pub intrinsic_marker_type: TypeId,
    pub unknown_type: TypeId,
    pub undefined_type: TypeId,
    pub undefined_widening_type: TypeId,
    pub missing_type: TypeId,
    pub undefined_or_missing_type: TypeId,
    pub optional_type: TypeId,
    pub null_type: TypeId,
    pub null_widening_type: TypeId,
    pub string_type: TypeId,
    pub number_type: TypeId,
    pub bigint_type: TypeId,
    pub regular_false_type: TypeId,
    pub false_type: TypeId,
    pub regular_true_type: TypeId,
    pub true_type: TypeId,
    pub boolean_type: TypeId,
    pub es_symbol_type: TypeId,
    pub void_type: TypeId,
    pub never_type: TypeId,
    pub silent_never_type: TypeId,
    pub implicit_never_type: TypeId,
    pub unreachable_never_type: TypeId,
    pub non_primitive_type: TypeId,
    pub string_or_number_type: TypeId,
    pub string_number_symbol_type: TypeId,
    pub number_or_bigint_type: TypeId,
    pub numeric_string_type: TypeId,
    pub template_constraint_type: TypeId,
    pub unique_literal_type: TypeId,

    pub empty_object_type: TypeId,
    pub empty_jsx_object_type: TypeId,
    pub empty_fresh_jsx_object_type: TypeId,
    pub empty_type_literal_symbol: SemanticSymbolId,
    pub empty_type_literal_type: TypeId,
    pub unknown_empty_object_type: TypeId,
    pub unknown_union_type: TypeId,
    pub empty_generic_type: TypeId,
    pub any_function_type: TypeId,
    pub no_constraint_type: TypeId,
    pub circular_constraint_type: TypeId,
    pub resolving_default_type: TypeId,
    pub marker_super_type: TypeId,
    pub marker_sub_type: TypeId,
    pub marker_other_type: TypeId,
    pub marker_super_type_for_check: TypeId,
    pub marker_sub_type_for_check: TypeId,

    pub no_type_predicate: TypePredicateId,
    pub any_signature: SignatureId,
    pub unknown_signature: SignatureId,
    pub resolving_signature: SignatureId,
    pub silent_never_signature: SignatureId,
    pub enum_number_index_info: IndexInfoId,
    pub any_base_type_index_info: IndexInfoId,

    pub empty_string_type: TypeId,
    pub zero_type: TypeId,
    pub zero_bigint_type: TypeId,
    pub typeof_type: TypeId,

    string_literal_types: HashMap<String, TypeId>,
    number_literal_types: HashMap<NumberLiteralCacheKey, TypeId>,
    bigint_literal_types: Vec<(PseudoBigInt, TypeId)>,
    union_types: HashMap<Vec<TypeId>, TypeId>,
    template_literal_types: HashMap<TemplateLiteralCacheKey, TypeId>,
}

impl SemanticStore<TypeRecord, TypeMapper> {
    /// Returns the already-initialized singleton set, if any.
    #[must_use]
    pub fn intrinsic_bootstrap(&self) -> Option<&IntrinsicBootstrap> {
        self.intrinsic_bootstrap.as_ref()
    }

    /// Initializes the exact dependency-closed intrinsic set once.
    ///
    /// A repeated request with identical options is idempotent. Different
    /// options or any prior checker-owned arena, sparse-link, or resolution
    /// write are rejected before this method changes semantic state. Prebound
    /// symbols/tables and registered AST scopes remain valid inputs.
    ///
    /// # Errors
    ///
    /// Returns [`IntrinsicBootstrapError::OptionsMismatch`] when a completed
    /// bootstrap used different options, or
    /// [`IntrinsicBootstrapError::NonPristineCheckerState`] when checker-owned
    /// state predates the first request.
    ///
    /// # Panics
    ///
    /// Panics if a canonical identity arena is exhausted or an internal pinned
    /// bootstrap shape is rejected by its canonical allocator.
    pub fn initialize_intrinsic_bootstrap(
        &mut self,
        options: IntrinsicBootstrapOptions,
    ) -> Result<&IntrinsicBootstrap, IntrinsicBootstrapError> {
        if let Some(initialized) = self
            .intrinsic_bootstrap
            .as_ref()
            .map(|bootstrap| bootstrap.options)
        {
            return if initialized == options {
                Ok(self
                    .intrinsic_bootstrap
                    .as_ref()
                    .expect("bootstrap presence was just observed"))
            } else {
                Err(IntrinsicBootstrapError::OptionsMismatch {
                    initialized,
                    requested: options,
                })
            };
        }

        let [
            node,
            symbol_node,
            type_node,
            enum_member,
            assertion,
            array_literal,
            switch_statement,
            jsx_element,
            signature,
            symbol_reference,
            value_symbol,
            mapped_symbol,
            deferred_symbol,
            alias_symbol,
            module_symbol,
            late_bound,
            export_type,
            members_and_exports,
            type_alias,
            declared_type,
            spread,
            variance,
            reverse_mapped_symbol,
            marked_assignment_symbol,
            containing_symbol,
            source_file,
        ] = self.checker_link_allocated_lengths();
        let (entries, resolution_start, boundaries, next_boundary_serial) =
            self.type_resolution_internal_state();
        let state = CheckerStateSnapshot {
            checker_symbols: self.symbol_store().checker_created_symbol_len(),
            merged_symbols: self.merged_symbol_len(),
            semantic_arenas: SemanticArenaCounts {
                types: self.type_len(),
                mappers: self.mapper_len(),
                signatures: self.signature_len(),
                predicates: self.type_predicate_len(),
                index_infos: self.index_info_len(),
                type_aliases: self.type_alias_len(),
                conditional_roots: self.conditional_root_len(),
                entity_names: self.entity_name_len(),
            },
            links: CheckerLinkCounts {
                node,
                symbol_node,
                type_node,
                enum_member,
                assertion,
                array_literal,
                switch_statement,
                jsx_element,
                signature,
                symbol_reference,
                value_symbol,
                mapped_symbol,
                deferred_symbol,
                alias_symbol,
                module_symbol,
                late_bound,
                export_type,
                members_and_exports,
                type_alias,
                declared_type,
                spread,
                variance,
                reverse_mapped_symbol,
                marked_assignment_symbol,
                containing_symbol,
                source_file,
            },
            type_resolution: TypeResolutionStateSnapshot {
                entries,
                resolution_start,
                boundaries,
                next_boundary_serial,
            },
            relations: self.relation_state_snapshot(),
        };
        if !state.is_pristine() {
            return Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                state,
            )));
        }

        let bootstrap = IntrinsicBootstrap::build(self, options);
        self.intrinsic_bootstrap = Some(bootstrap);
        Ok(self
            .intrinsic_bootstrap
            .as_ref()
            .expect("bootstrap was just installed"))
    }
}

impl IntrinsicBootstrap {
    /// Looks up the exact string-literal cache populated during bootstrap.
    #[must_use]
    pub fn cached_string_literal_type(&self, value: &str) -> Option<TypeId> {
        self.string_literal_types.get(value).copied()
    }

    /// Looks up the exact number-literal cache populated during bootstrap.
    ///
    /// NaN is absent because pinned `NewChecker` does not initialize `nanType`.
    #[must_use]
    pub fn cached_number_literal_type(&self, value: Number) -> Option<TypeId> {
        NumberLiteralCacheKey::from_number(value)
            .and_then(|key| self.number_literal_types.get(&key).copied())
    }

    /// Looks up the exact bigint-literal cache populated during bootstrap.
    #[must_use]
    pub fn cached_bigint_literal_type(&self, value: &PseudoBigInt) -> Option<TypeId> {
        self.bigint_literal_types
            .iter()
            .find_map(|(cached, id)| (cached == value).then_some(*id))
    }

    /// Looks up an already-normalized, sorted bootstrap union key.
    ///
    /// Constituent flattening and nullable/literal reduction belong to the
    /// future general `getUnionType`; this read API never approximates them.
    #[must_use]
    pub fn cached_union_type(&self, normalized_types: &[TypeId]) -> Option<TypeId> {
        self.union_types.get(normalized_types).copied()
    }

    /// Looks up an already-normalized bootstrap template-literal key.
    #[must_use]
    pub fn cached_template_literal_type(
        &self,
        normalized_texts: &[String],
        normalized_types: &[TypeId],
    ) -> Option<TypeId> {
        self.template_literal_types.iter().find_map(|(key, id)| {
            (key.texts.as_slice() == normalized_texts && key.types.as_slice() == normalized_types)
                .then_some(*id)
        })
    }

    /// Number of string-literal entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn string_literal_cache_len(&self) -> usize {
        self.string_literal_types.len()
    }

    /// Number of number-literal entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn number_literal_cache_len(&self) -> usize {
        self.number_literal_types.len()
    }

    /// Number of bigint-literal entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn bigint_literal_cache_len(&self) -> usize {
        self.bigint_literal_types.len()
    }

    /// Number of normalized union entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn union_cache_len(&self) -> usize {
        self.union_types.len()
    }

    /// Number of template-literal entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn template_literal_cache_len(&self) -> usize {
        self.template_literal_types.len()
    }

    #[allow(clippy::too_many_lines)] // Preserves the observable pinned initialization order.
    fn build(
        store: &mut SemanticStore<TypeRecord, TypeMapper>,
        options: IntrinsicBootstrapOptions,
    ) -> Self {
        let mut string_literal_types = HashMap::new();
        let mut number_literal_types = HashMap::new();
        let mut bigint_literal_types = Vec::new();
        let mut union_types = HashMap::new();
        let mut template_literal_types = HashMap::new();

        let globals = store.alloc_symbol_table();
        let undefined_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "undefined");
        let arguments_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "arguments");
        let require_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "require");
        let unknown_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "unknown");
        let global_this_symbol = store.alloc_transient_symbol(
            SymbolFlags::MODULE,
            EscapedName::source("globalThis"),
            CheckFlags::READONLY,
        );
        assert!(store.set_symbol_relationships(
            global_this_symbol,
            None,
            Some(globals),
            None,
            None,
        ));
        assert_eq!(
            store.insert_symbol(
                globals,
                EscapedName::source("globalThis"),
                global_this_symbol,
            ),
            Some(None),
        );

        let any_type = intrinsic(store, TypeFlags::ANY, "any");
        let auto_type = intrinsic_ex(
            store,
            TypeFlags::ANY,
            "any",
            ObjectFlags::NON_INFERRABLE_TYPE,
        );
        let wildcard_type = intrinsic(store, TypeFlags::ANY, "any");
        let blocked_string_type = intrinsic(store, TypeFlags::ANY, "any");
        let error_type = intrinsic(store, TypeFlags::ANY, "error");
        let unresolved_type = intrinsic(store, TypeFlags::ANY, "unresolved");
        let non_inferrable_any_type = intrinsic_ex(
            store,
            TypeFlags::ANY,
            "any",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        let intrinsic_marker_type = intrinsic(store, TypeFlags::ANY, "intrinsic");
        let unknown_type = intrinsic(store, TypeFlags::UNKNOWN, "unknown");
        let undefined_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let undefined_widening_type = if options.strict_null_checks {
            undefined_type
        } else {
            intrinsic_ex(
                store,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            )
        };
        let missing_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let undefined_or_missing_type = if options.exact_optional_property_types {
            missing_type
        } else {
            undefined_type
        };
        let optional_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let null_type = intrinsic(store, TypeFlags::NULL, "null");
        let null_widening_type = if options.strict_null_checks {
            null_type
        } else {
            intrinsic_ex(
                store,
                TypeFlags::NULL,
                "null",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            )
        };
        let string_type = intrinsic(store, TypeFlags::STRING, "string");
        let number_type = intrinsic(store, TypeFlags::NUMBER, "number");
        let bigint_type = intrinsic(store, TypeFlags::BIG_INT, "bigint");

        let regular_false_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(false),
            RegularLiteralLink::SelfType,
        );
        let false_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(false),
            RegularLiteralLink::Type(regular_false_type),
        );
        assert!(store.set_literal_links(regular_false_type, Some(false_type), regular_false_type,));
        assert!(store.set_literal_links(false_type, Some(false_type), regular_false_type,));
        let regular_true_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(true),
            RegularLiteralLink::SelfType,
        );
        let true_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(true),
            RegularLiteralLink::Type(regular_true_type),
        );
        assert!(store.set_literal_links(regular_true_type, Some(true_type), regular_true_type,));
        assert!(store.set_literal_links(true_type, Some(true_type), regular_true_type,));
        let boolean_type = fixed_union(
            store,
            &mut union_types,
            vec![regular_false_type, regular_true_type],
            ObjectFlags::PRIMITIVE_UNION,
            true,
        );

        let es_symbol_type = intrinsic(store, TypeFlags::ES_SYMBOL, "symbol");
        let void_type = intrinsic(store, TypeFlags::VOID, "void");
        let never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let silent_never_type = intrinsic_ex(
            store,
            TypeFlags::NEVER,
            "never",
            ObjectFlags::NON_INFERRABLE_TYPE,
        );
        let implicit_never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let unreachable_never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let non_primitive_type = intrinsic(store, TypeFlags::NON_PRIMITIVE, "object");
        let string_or_number_type = fixed_union(
            store,
            &mut union_types,
            vec![string_type, number_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let string_number_symbol_type = fixed_union(
            store,
            &mut union_types,
            vec![string_type, number_type, es_symbol_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let number_or_bigint_type = fixed_union(
            store,
            &mut union_types,
            vec![number_type, bigint_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let numeric_string_type = cached_template_literal(
            store,
            &mut template_literal_types,
            vec![String::new(), String::new()],
            vec![number_type],
        );
        let template_constraint_types = if options.strict_null_checks {
            vec![
                undefined_type,
                null_type,
                string_type,
                number_type,
                bigint_type,
                regular_false_type,
                regular_true_type,
            ]
        } else {
            // Pinned addTypeToUnion records nullable includes but does not insert
            // nullable constituents when strict null checking is disabled.
            vec![
                string_type,
                number_type,
                bigint_type,
                regular_false_type,
                regular_true_type,
            ]
        };
        let template_constraint_type = fixed_union(
            store,
            &mut union_types,
            template_constraint_types,
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let unique_literal_type = intrinsic(store, TypeFlags::NEVER, "never");

        // Five callback-owned mapper allocations occur here upstream. They are
        // deliberately absent until canonical TypeMapper can own executable behavior.
        let empty_object_type = anonymous(store, None);
        let empty_jsx_object_type = anonymous(store, None);
        let empty_fresh_jsx_object_type = anonymous(store, None);
        let empty_type_literal_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
            CheckFlags::NONE,
        );
        let empty_type_literal_type = anonymous(store, Some(empty_type_literal_symbol));
        let unknown_empty_object_type = anonymous(store, None);
        let unknown_union_type = if options.strict_null_checks {
            fixed_union(
                store,
                &mut union_types,
                vec![undefined_type, null_type, unknown_empty_object_type],
                ObjectFlags::NONE,
                false,
            )
        } else {
            unknown_type
        };
        let empty_generic_type = anonymous(store, None);
        assert!(store.set_object_instantiations(
            empty_generic_type,
            TypeCacheState::Allocated(HashMap::new()),
        ));
        let any_function_type = anonymous(store, None);
        assert!(store.add_type_object_flags(any_function_type, ObjectFlags::NON_INFERRABLE_TYPE,));
        let no_constraint_type = anonymous(store, None);
        let circular_constraint_type = anonymous(store, None);
        let resolving_default_type = anonymous(store, None);
        let marker_super_type = type_parameter(store);
        let marker_sub_type = type_parameter(store);
        assert!(store.set_type_parameter_resolution(
            marker_sub_type,
            Some(marker_super_type),
            None,
            None,
            None,
        ));
        let marker_other_type = type_parameter(store);
        let marker_super_type_for_check = type_parameter(store);
        let marker_sub_type_for_check = type_parameter(store);
        assert!(store.set_type_parameter_resolution(
            marker_sub_type_for_check,
            Some(marker_super_type_for_check),
            None,
            None,
            None,
        ));

        let no_type_predicate = store
            .alloc_type_predicate(
                TypePredicateKind::Identifier,
                0,
                "<<unresolved>>",
                Some(any_type),
            )
            .expect("the pinned no-type predicate references this store");
        let any_signature = empty_signature(store, any_type);
        let unknown_signature = empty_signature(store, error_type);
        let resolving_signature = empty_signature(store, any_type);
        let silent_never_signature = empty_signature(store, silent_never_type);
        let enum_number_index_info = store
            .alloc_index_info(number_type, string_type, true, None, Vec::new())
            .expect("the pinned enum number index info references this store");
        let any_base_type_index_info = store
            .alloc_index_info(string_type, any_type, false, None, Vec::new())
            .expect("the pinned any-base index info references this store");

        let empty_string_type =
            cached_string_literal(store, &mut string_literal_types, String::new());
        let zero_type = cached_number_literal(store, &mut number_literal_types, Number::new(0.0));
        let zero_bigint_type =
            cached_bigint_literal(store, &mut bigint_literal_types, PseudoBigInt::default());
        let typeof_types = [
            "bigint",
            "boolean",
            "function",
            "number",
            "object",
            "string",
            "symbol",
            "undefined",
        ]
        .into_iter()
        .map(|value| cached_string_literal(store, &mut string_literal_types, value.to_owned()))
        .collect();
        let typeof_type = fixed_union(
            store,
            &mut union_types,
            typeof_types,
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );

        Self {
            options,
            globals,
            undefined_symbol,
            arguments_symbol,
            require_symbol,
            unknown_symbol,
            global_this_symbol,
            any_type,
            auto_type,
            wildcard_type,
            blocked_string_type,
            error_type,
            unresolved_type,
            non_inferrable_any_type,
            intrinsic_marker_type,
            unknown_type,
            undefined_type,
            undefined_widening_type,
            missing_type,
            undefined_or_missing_type,
            optional_type,
            null_type,
            null_widening_type,
            string_type,
            number_type,
            bigint_type,
            regular_false_type,
            false_type,
            regular_true_type,
            true_type,
            boolean_type,
            es_symbol_type,
            void_type,
            never_type,
            silent_never_type,
            implicit_never_type,
            unreachable_never_type,
            non_primitive_type,
            string_or_number_type,
            string_number_symbol_type,
            number_or_bigint_type,
            numeric_string_type,
            template_constraint_type,
            unique_literal_type,
            empty_object_type,
            empty_jsx_object_type,
            empty_fresh_jsx_object_type,
            empty_type_literal_symbol,
            empty_type_literal_type,
            unknown_empty_object_type,
            unknown_union_type,
            empty_generic_type,
            any_function_type,
            no_constraint_type,
            circular_constraint_type,
            resolving_default_type,
            marker_super_type,
            marker_sub_type,
            marker_other_type,
            marker_super_type_for_check,
            marker_sub_type_for_check,
            no_type_predicate,
            any_signature,
            unknown_signature,
            resolving_signature,
            silent_never_signature,
            enum_number_index_info,
            any_base_type_index_info,
            empty_string_type,
            zero_type,
            zero_bigint_type,
            typeof_type,
            string_literal_types,
            number_literal_types,
            bigint_literal_types,
            union_types,
            template_literal_types,
        }
    }
}

fn transient_symbol(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: SymbolFlags,
    name: &str,
) -> SemanticSymbolId {
    store.alloc_transient_symbol(flags, EscapedName::source(name), CheckFlags::NONE)
}

fn intrinsic(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    name: &str,
) -> TypeId {
    store
        .alloc_intrinsic_type(flags, name)
        .expect("the pinned intrinsic shape is valid")
}

fn intrinsic_ex(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    name: &str,
    object_flags: ObjectFlags,
) -> TypeId {
    store
        .alloc_intrinsic_type_ex(flags, name, object_flags)
        .expect("the pinned extended intrinsic shape is valid")
}

fn literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    value: LiteralValue,
    regular_type: RegularLiteralLink,
) -> TypeId {
    store
        .alloc_literal_type(flags, value, regular_type)
        .expect("the pinned literal shape and provenance are valid")
}

fn fixed_union(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<Vec<TypeId>, TypeId>,
    types: Vec<TypeId>,
    object_flags: ObjectFlags,
    is_boolean: bool,
) -> TypeId {
    if let Some(cached) = cache.get(types.as_slice()) {
        return *cached;
    }
    let key = types.clone();
    let union = store
        .alloc_union_type(object_flags, types)
        .expect("the pinned sorted union constituents belong to this store");
    if is_boolean {
        assert!(store.add_type_flags(union, TypeFlags::BOOLEAN));
    }
    assert_eq!(cache.insert(key, union), None);
    union
}

fn cached_template_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<TemplateLiteralCacheKey, TypeId>,
    texts: Vec<String>,
    types: Vec<TypeId>,
) -> TypeId {
    let key = TemplateLiteralCacheKey {
        texts: texts.clone(),
        types: types.clone(),
    };
    if let Some(cached) = cache.get(&key) {
        return *cached;
    }
    let template = store
        .alloc_template_literal_type(texts, types)
        .expect("the pinned normalized template literal is valid");
    assert_eq!(cache.insert(key, template), None);
    template
}

fn cached_string_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<String, TypeId>,
    value: String,
) -> TypeId {
    if let Some(cached) = cache.get(&value) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::STRING_LITERAL,
        LiteralValue::String(value.clone()),
        RegularLiteralLink::SelfType,
    );
    assert_eq!(cache.insert(value, literal), None);
    literal
}

fn cached_number_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<NumberLiteralCacheKey, TypeId>,
    value: Number,
) -> TypeId {
    let key = NumberLiteralCacheKey::from_number(value)
        .expect("NewChecker bootstrap never requests a NaN literal");
    if let Some(cached) = cache.get(&key) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::NUMBER_LITERAL,
        LiteralValue::Number(value),
        RegularLiteralLink::SelfType,
    );
    assert_eq!(cache.insert(key, literal), None);
    literal
}

fn cached_bigint_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut Vec<(PseudoBigInt, TypeId)>,
    value: PseudoBigInt,
) -> TypeId {
    if let Some((_, cached)) = cache.iter().find(|(cached, _)| cached == &value) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::BIG_INT_LITERAL,
        LiteralValue::BigInt(value.clone()),
        RegularLiteralLink::SelfType,
    );
    cache.push((value, literal));
    literal
}

fn anonymous(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    symbol: Option<SemanticSymbolId>,
) -> TypeId {
    let object = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, symbol)
        .expect("the pinned anonymous type shape and symbol provenance are valid");
    assert!(store.set_structured_type_members(object, None, None, None, None, None));
    object
}

fn type_parameter(store: &mut SemanticStore<TypeRecord, TypeMapper>) -> TypeId {
    store
        .alloc_type_parameter(None)
        .expect("the pinned marker type parameter is valid")
}

fn empty_signature(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    return_type: TypeId,
) -> SignatureId {
    store
        .alloc_signature(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(return_type),
            None,
            0,
        )
        .expect("the pinned sentinel signature references this store")
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{
        AstScope, CheckFlags, EscapedName, InternalSymbolName, SymbolData, SymbolFlags, SymbolStore,
    };
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, DecoratorSignatureState, EffectsSignatureState,
        ResolvedSignatureState, SignatureLinks,
        type_records::{LiteralTypeData, TypeData},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    fn initialized(options: IntrinsicBootstrapOptions) -> TestStore {
        let mut store = TestStore::new();
        store.initialize_intrinsic_bootstrap(options).unwrap();
        store
    }

    #[test]
    fn sparse_links_canonicalize_bootstrap_sentinel_id_encodings() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (resolving_signature, unknown_signature, any_signature, unknown_symbol) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.resolving_signature,
                bootstrap.unknown_signature,
                bootstrap.any_signature,
                bootstrap.unknown_symbol,
            )
        };
        let parsed = parse_source_file("factory();");
        let file = FileId::new(91);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let call = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::CallExpression).then_some(id))
            .unwrap();
        let call = NodeRef::new(parsed.arena.id(), file, call);

        assert!(store.set_signature_links(
            call,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(resolving_signature),
                effects_signature: EffectsSignatureState::Resolved(unknown_signature),
                decorator_signature: DecoratorSignatureState::Resolved(any_signature),
            }
        ));
        assert_eq!(
            store.signature_links(call),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolving,
                effects_signature: EffectsSignatureState::NoEffects,
                decorator_signature: DecoratorSignatureState::NotApplicable,
            })
        );

        let alias = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::ALIAS,
                EscapedName::source("alias"),
            ))
            .unwrap();
        assert!(store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                alias_target: AliasTargetState::Resolved(unknown_symbol),
                ..AliasSymbolLinks::default()
            }
        ));
        assert_eq!(
            store.alias_symbol_links(alias).unwrap().alias_target,
            AliasTargetState::Unknown
        );
    }

    fn record(store: &TestStore, id: TypeId) -> &TypeRecord {
        store.type_payload(id).unwrap()
    }

    fn literal_data(store: &TestStore, id: TypeId) -> &LiteralTypeData {
        let TypeData::Literal(data) = record(store, id).data() else {
            panic!("expected literal payload")
        };
        data
    }

    fn union_types(store: &TestStore, id: TypeId) -> &[TypeId] {
        let TypeData::Union(data) = record(store, id).data() else {
            panic!("expected union payload")
        };
        &data.union.types
    }

    fn assert_intrinsic(
        store: &TestStore,
        id: TypeId,
        flags: TypeFlags,
        name: &str,
        object_flags: ObjectFlags,
    ) {
        let type_record = record(store, id);
        assert_eq!(type_record.flags(), flags);
        assert_eq!(type_record.object_flags(), object_flags);
        assert_eq!(type_record.symbol(), None);
        assert_eq!(type_record.alias(), None);
        let TypeData::Intrinsic(data) = type_record.data() else {
            panic!("expected intrinsic payload")
        };
        assert_eq!(data.intrinsic_name, name);
    }

    fn assert_union(
        store: &TestStore,
        id: TypeId,
        flags: TypeFlags,
        object_flags: ObjectFlags,
        types: &[TypeId],
    ) {
        assert_eq!(record(store, id).flags(), flags);
        assert_eq!(record(store, id).object_flags(), object_flags);
        assert_eq!(union_types(store, id), types);
    }

    fn semantic_counts(store: &TestStore) -> SemanticArenaCounts {
        SemanticArenaCounts {
            types: store.type_len(),
            mappers: store.mapper_len(),
            signatures: store.signature_len(),
            predicates: store.type_predicate_len(),
            index_infos: store.index_info_len(),
            type_aliases: store.type_alias_len(),
            conditional_roots: store.conditional_root_len(),
            entity_names: store.entity_name_len(),
        }
    }

    fn checker_state(store: &TestStore) -> CheckerStateSnapshot {
        let [
            node,
            symbol_node,
            type_node,
            enum_member,
            assertion,
            array_literal,
            switch_statement,
            jsx_element,
            signature,
            symbol_reference,
            value_symbol,
            mapped_symbol,
            deferred_symbol,
            alias_symbol,
            module_symbol,
            late_bound,
            export_type,
            members_and_exports,
            type_alias,
            declared_type,
            spread,
            variance,
            reverse_mapped_symbol,
            marked_assignment_symbol,
            containing_symbol,
            source_file,
        ] = store.checker_link_allocated_lengths();
        let (entries, resolution_start, boundaries, next_boundary_serial) =
            store.type_resolution_internal_state();
        CheckerStateSnapshot {
            checker_symbols: store.symbol_store().checker_created_symbol_len(),
            merged_symbols: store.merged_symbol_len(),
            semantic_arenas: semantic_counts(store),
            links: CheckerLinkCounts {
                node,
                symbol_node,
                type_node,
                enum_member,
                assertion,
                array_literal,
                switch_statement,
                jsx_element,
                signature,
                symbol_reference,
                value_symbol,
                mapped_symbol,
                deferred_symbol,
                alias_symbol,
                module_symbol,
                late_bound,
                export_type,
                members_and_exports,
                type_alias,
                declared_type,
                spread,
                variance,
                reverse_mapped_symbol,
                marked_assignment_symbol,
                containing_symbol,
                source_file,
            },
            type_resolution: TypeResolutionStateSnapshot {
                entries,
                resolution_start,
                boundaries,
                next_boundary_serial,
            },
            relations: store.relation_state_snapshot(),
        }
    }

    fn assert_all_distinct(ids: &[TypeId]) {
        assert_eq!(ids.iter().copied().collect::<HashSet<_>>().len(), ids.len());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One table pins the full upstream allocation sequence.
    fn strict_bootstrap_preserves_pinned_symbols_intrinsics_and_allocation_order() {
        let options = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        };
        let store = initialized(options);
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_eq!(bootstrap.globals.get(), 1);
        assert_eq!(bootstrap.undefined_symbol.get(), 1);
        assert_eq!(bootstrap.arguments_symbol.get(), 2);
        assert_eq!(bootstrap.require_symbol.get(), 3);
        assert_eq!(bootstrap.unknown_symbol.get(), 4);
        assert_eq!(bootstrap.global_this_symbol.get(), 5);
        assert_eq!(bootstrap.empty_type_literal_symbol.get(), 6);
        for (id, name) in [
            (bootstrap.undefined_symbol, "undefined"),
            (bootstrap.arguments_symbol, "arguments"),
            (bootstrap.require_symbol, "require"),
            (bootstrap.unknown_symbol, "unknown"),
        ] {
            let symbol = store.symbol(id).unwrap();
            assert_eq!(
                symbol.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            );
            assert_eq!(symbol.check_flags(), CheckFlags::NONE);
            assert_eq!(symbol.name().as_utf8(), Some(name));
        }
        let global_this = store.symbol(bootstrap.global_this_symbol).unwrap();
        assert_eq!(
            global_this.flags(),
            SymbolFlags::MODULE | SymbolFlags::TRANSIENT,
        );
        assert_eq!(global_this.check_flags(), CheckFlags::READONLY);
        assert_eq!(global_this.exports(), Some(bootstrap.globals));
        assert_eq!(
            store
                .symbol_table(bootstrap.globals)
                .unwrap()
                .get_source("globalThis"),
            Some(bootstrap.global_this_symbol),
        );
        let type_literal = store.symbol(bootstrap.empty_type_literal_symbol).unwrap();
        assert_eq!(
            type_literal.flags(),
            SymbolFlags::TYPE_LITERAL | SymbolFlags::TRANSIENT,
        );
        assert_eq!(
            type_literal.name().as_bytes(),
            InternalSymbolName::Type.as_bytes(),
        );

        let allocated_in_order = [
            bootstrap.any_type,
            bootstrap.auto_type,
            bootstrap.wildcard_type,
            bootstrap.blocked_string_type,
            bootstrap.error_type,
            bootstrap.unresolved_type,
            bootstrap.non_inferrable_any_type,
            bootstrap.intrinsic_marker_type,
            bootstrap.unknown_type,
            bootstrap.undefined_type,
            bootstrap.missing_type,
            bootstrap.optional_type,
            bootstrap.null_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.bigint_type,
            bootstrap.regular_false_type,
            bootstrap.false_type,
            bootstrap.regular_true_type,
            bootstrap.true_type,
            bootstrap.boolean_type,
            bootstrap.es_symbol_type,
            bootstrap.void_type,
            bootstrap.never_type,
            bootstrap.silent_never_type,
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type,
            bootstrap.non_primitive_type,
            bootstrap.string_or_number_type,
            bootstrap.string_number_symbol_type,
            bootstrap.number_or_bigint_type,
            bootstrap.numeric_string_type,
            bootstrap.template_constraint_type,
            bootstrap.unique_literal_type,
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.empty_type_literal_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.unknown_union_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
            bootstrap.marker_super_type,
            bootstrap.marker_sub_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
            bootstrap.marker_sub_type_for_check,
            bootstrap.empty_string_type,
            bootstrap.zero_type,
            bootstrap.zero_bigint_type,
        ];
        assert_eq!(
            allocated_in_order.map(TypeId::get),
            std::array::from_fn(|index| u32::try_from(index + 1).unwrap()),
        );
        assert_eq!(bootstrap.undefined_widening_type, bootstrap.undefined_type);
        assert_eq!(bootstrap.null_widening_type, bootstrap.null_type);
        assert_eq!(bootstrap.undefined_or_missing_type, bootstrap.missing_type);
        assert_eq!(bootstrap.typeof_type.get(), 62);
        assert_eq!(store.type_len(), 62);

        for (id, flags, name, object_flags) in [
            (bootstrap.any_type, TypeFlags::ANY, "any", ObjectFlags::NONE),
            (
                bootstrap.auto_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NON_INFERRABLE_TYPE,
            ),
            (
                bootstrap.wildcard_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.blocked_string_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.error_type,
                TypeFlags::ANY,
                "error",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.unresolved_type,
                TypeFlags::ANY,
                "unresolved",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.non_inferrable_any_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            ),
            (
                bootstrap.intrinsic_marker_type,
                TypeFlags::ANY,
                "intrinsic",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.unknown_type,
                TypeFlags::UNKNOWN,
                "unknown",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.undefined_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.missing_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.optional_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.null_type,
                TypeFlags::NULL,
                "null",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.string_type,
                TypeFlags::STRING,
                "string",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.number_type,
                TypeFlags::NUMBER,
                "number",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.bigint_type,
                TypeFlags::BIG_INT,
                "bigint",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.silent_never_type,
                TypeFlags::NEVER,
                "never",
                ObjectFlags::NON_INFERRABLE_TYPE,
            ),
            (
                bootstrap.non_primitive_type,
                TypeFlags::NON_PRIMITIVE,
                "object",
                ObjectFlags::NONE,
            ),
        ] {
            assert_intrinsic(&store, id, flags, name, object_flags);
        }
        assert_ne!(bootstrap.any_type, bootstrap.wildcard_type);
        assert_ne!(bootstrap.wildcard_type, bootstrap.blocked_string_type);
        assert_ne!(bootstrap.never_type, bootstrap.implicit_never_type);
        assert_ne!(
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type
        );
        assert_ne!(bootstrap.unique_literal_type, bootstrap.never_type);
        assert_all_distinct(&[
            bootstrap.any_type,
            bootstrap.wildcard_type,
            bootstrap.blocked_string_type,
        ]);
        assert_all_distinct(&[
            bootstrap.undefined_type,
            bootstrap.missing_type,
            bootstrap.optional_type,
        ]);
        assert_all_distinct(&[
            bootstrap.never_type,
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type,
            bootstrap.unique_literal_type,
        ]);
        assert_all_distinct(&[
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
        ]);
        assert_all_distinct(&[
            bootstrap.marker_super_type,
            bootstrap.marker_sub_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
            bootstrap.marker_sub_type_for_check,
        ]);
        assert_ne!(bootstrap.any_signature, bootstrap.resolving_signature);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keeps interdependent identity assertions together.
    fn bootstrap_preserves_literal_union_object_and_sentinel_records() {
        let store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            bootstrap.undefined_or_missing_type,
            bootstrap.undefined_type,
        );

        for (regular, fresh, value) in [
            (bootstrap.regular_false_type, bootstrap.false_type, false),
            (bootstrap.regular_true_type, bootstrap.true_type, true),
        ] {
            let regular_data = literal_data(&store, regular);
            assert_eq!(regular_data.value, LiteralValue::Boolean(value));
            assert_eq!(regular_data.regular_type, regular);
            assert_eq!(regular_data.fresh_type, Some(fresh));
            let fresh_data = literal_data(&store, fresh);
            assert_eq!(fresh_data.value, LiteralValue::Boolean(value));
            assert_eq!(fresh_data.regular_type, regular);
            assert_eq!(fresh_data.fresh_type, Some(fresh));
        }
        assert_eq!(
            record(&store, bootstrap.boolean_type).flags(),
            TypeFlags::UNION | TypeFlags::BOOLEAN,
        );
        assert_eq!(
            record(&store, bootstrap.boolean_type).object_flags(),
            ObjectFlags::PRIMITIVE_UNION,
        );
        assert_eq!(
            union_types(&store, bootstrap.boolean_type),
            [bootstrap.regular_false_type, bootstrap.regular_true_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.string_or_number_type),
            [bootstrap.string_type, bootstrap.number_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.string_number_symbol_type),
            [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.es_symbol_type,
            ],
        );
        assert_eq!(
            union_types(&store, bootstrap.number_or_bigint_type),
            [bootstrap.number_type, bootstrap.bigint_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.template_constraint_type),
            [
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.regular_false_type,
                bootstrap.regular_true_type,
            ],
        );
        assert_eq!(
            union_types(&store, bootstrap.unknown_union_type),
            [
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ],
        );
        assert_eq!(
            record(&store, bootstrap.unknown_union_type).object_flags(),
            ObjectFlags::NONE,
        );
        assert_union(
            &store,
            bootstrap.boolean_type,
            TypeFlags::UNION | TypeFlags::BOOLEAN,
            ObjectFlags::PRIMITIVE_UNION,
            &[bootstrap.regular_false_type, bootstrap.regular_true_type],
        );
        for (id, types) in [
            (
                bootstrap.string_or_number_type,
                vec![bootstrap.string_type, bootstrap.number_type],
            ),
            (
                bootstrap.string_number_symbol_type,
                vec![
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.es_symbol_type,
                ],
            ),
            (
                bootstrap.number_or_bigint_type,
                vec![bootstrap.number_type, bootstrap.bigint_type],
            ),
            (
                bootstrap.template_constraint_type,
                vec![
                    bootstrap.undefined_type,
                    bootstrap.null_type,
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.bigint_type,
                    bootstrap.regular_false_type,
                    bootstrap.regular_true_type,
                ],
            ),
        ] {
            assert_union(
                &store,
                id,
                TypeFlags::UNION,
                ObjectFlags::PRIMITIVE_UNION,
                &types,
            );
        }
        assert_union(
            &store,
            bootstrap.unknown_union_type,
            TypeFlags::UNION,
            ObjectFlags::NONE,
            &[
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ],
        );
        let TypeData::TemplateLiteral(numeric_string) =
            record(&store, bootstrap.numeric_string_type).data()
        else {
            panic!("expected template literal payload")
        };
        assert_eq!(numeric_string.texts, ["", ""]);
        assert_eq!(numeric_string.types, [bootstrap.number_type]);

        for id in [
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.empty_type_literal_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
        ] {
            let type_record = record(&store, id);
            assert!(type_record.object_flags().contains(ObjectFlags::ANONYMOUS));
            assert!(
                type_record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED),
            );
            let TypeData::Object(data) = type_record.data() else {
                panic!("expected plain object payload")
            };
            assert_eq!(data.structured.members, None);
            assert_eq!(data.structured.properties, None);
            assert_eq!(data.structured.signatures, None);
            assert_eq!(data.structured.call_signature_count, 0);
            assert_eq!(data.structured.index_infos, None);
        }
        assert_eq!(
            record(&store, bootstrap.empty_type_literal_type).symbol(),
            Some(bootstrap.empty_type_literal_symbol),
        );
        let TypeData::Object(empty_generic) = record(&store, bootstrap.empty_generic_type).data()
        else {
            panic!("expected empty generic object")
        };
        assert!(matches!(
            &empty_generic.instantiations,
            TypeCacheState::Allocated(cache) if cache.is_empty()
        ));
        assert!(
            record(&store, bootstrap.any_function_type)
                .object_flags()
                .contains(ObjectFlags::NON_INFERRABLE_TYPE),
        );

        let TypeData::TypeParameter(marker_sub) = record(&store, bootstrap.marker_sub_type).data()
        else {
            panic!("expected marker type parameter")
        };
        assert_eq!(marker_sub.constraint, Some(bootstrap.marker_super_type));
        let TypeData::TypeParameter(marker_sub_for_check) =
            record(&store, bootstrap.marker_sub_type_for_check).data()
        else {
            panic!("expected check marker type parameter")
        };
        assert_eq!(
            marker_sub_for_check.constraint,
            Some(bootstrap.marker_super_type_for_check),
        );
        for id in [
            bootstrap.marker_super_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
        ] {
            let TypeData::TypeParameter(data) = record(&store, id).data() else {
                panic!("expected marker type parameter")
            };
            assert_eq!(data.constraint, None);
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            assert_eq!(data.resolved_default_type, None);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Pins every default in the sentinel record cluster.
    fn bootstrap_preserves_predicate_signature_index_and_literal_tail_defaults() {
        let store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        let predicate = store.type_predicate(bootstrap.no_type_predicate).unwrap();
        assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
        assert_eq!(predicate.parameter_index(), 0);
        assert_eq!(predicate.parameter_name(), "<<unresolved>>");
        assert_eq!(predicate.type_id(), Some(bootstrap.any_type));
        for (id, return_type) in [
            (bootstrap.any_signature, bootstrap.any_type),
            (bootstrap.unknown_signature, bootstrap.error_type),
            (bootstrap.resolving_signature, bootstrap.any_type),
            (
                bootstrap.silent_never_signature,
                bootstrap.silent_never_type,
            ),
        ] {
            let signature = store.signature(id).unwrap();
            assert_eq!(signature.flags(), SignatureFlags::NONE);
            assert_eq!(signature.min_argument_count(), 0);
            assert_eq!(signature.resolved_min_argument_count(), -1);
            assert_eq!(signature.declaration(), None);
            assert!(signature.type_parameters().is_empty());
            assert!(signature.parameters().is_empty());
            assert_eq!(signature.this_parameter(), None);
            assert_eq!(signature.resolved_return_type(), Some(return_type));
            assert_eq!(signature.resolved_type_predicate(), None);
            assert_eq!(signature.target(), None);
            assert_eq!(signature.mapper(), None);
            assert_eq!(signature.isolated_signature_type(), None);
            assert_eq!(signature.composite(), None);
        }
        let enum_index = store.index_info(bootstrap.enum_number_index_info).unwrap();
        assert_eq!(enum_index.key_type(), bootstrap.number_type);
        assert_eq!(enum_index.value_type(), bootstrap.string_type);
        assert!(enum_index.is_readonly());
        assert_eq!(enum_index.declaration(), None);
        assert_eq!(enum_index.index_symbol(), None);
        assert!(enum_index.components().is_empty());
        let any_base_index = store
            .index_info(bootstrap.any_base_type_index_info)
            .unwrap();
        assert_eq!(any_base_index.key_type(), bootstrap.string_type);
        assert_eq!(any_base_index.value_type(), bootstrap.any_type);
        assert!(!any_base_index.is_readonly());

        assert_eq!(
            literal_data(&store, bootstrap.empty_string_type).value,
            LiteralValue::String(String::new()),
        );
        assert_eq!(
            literal_data(&store, bootstrap.zero_type).value,
            LiteralValue::Number(Number::new(0.0)),
        );
        assert_eq!(
            literal_data(&store, bootstrap.zero_bigint_type).value,
            LiteralValue::BigInt(PseudoBigInt::default()),
        );
        for id in [
            bootstrap.empty_string_type,
            bootstrap.zero_type,
            bootstrap.zero_bigint_type,
        ] {
            let data = literal_data(&store, id);
            assert_eq!(data.regular_type, id);
            assert_eq!(data.fresh_type, None);
        }
        let typeof_values = union_types(&store, bootstrap.typeof_type)
            .iter()
            .map(|id| match &literal_data(&store, *id).value {
                LiteralValue::String(value) => value.as_str(),
                _ => panic!("typeof witness must be a string literal"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            typeof_values,
            [
                "bigint",
                "boolean",
                "function",
                "number",
                "object",
                "string",
                "symbol",
                "undefined",
            ],
        );
        assert_eq!(
            record(&store, bootstrap.typeof_type).object_flags(),
            ObjectFlags::PRIMITIVE_UNION,
        );
        assert_eq!(bootstrap.string_literal_cache_len(), 9);
        assert_eq!(bootstrap.number_literal_cache_len(), 1);
        assert_eq!(bootstrap.bigint_literal_cache_len(), 1);
        assert_eq!(bootstrap.union_cache_len(), 7);
        assert_eq!(bootstrap.template_literal_cache_len(), 1);
        assert_eq!(
            bootstrap.cached_string_literal_type(""),
            Some(bootstrap.empty_string_type),
        );
        assert_eq!(
            bootstrap.cached_number_literal_type(Number::new(0.0)),
            Some(bootstrap.zero_type),
        );
        assert_eq!(
            bootstrap.cached_number_literal_type(Number::new(-0.0)),
            Some(bootstrap.zero_type),
        );
        assert_eq!(bootstrap.cached_number_literal_type(Number::nan()), None);
        assert_eq!(
            bootstrap.cached_bigint_literal_type(&PseudoBigInt::default()),
            Some(bootstrap.zero_bigint_type),
        );
        for id in union_types(&store, bootstrap.typeof_type) {
            let LiteralValue::String(value) = &literal_data(&store, *id).value else {
                panic!("typeof witness must be a string literal")
            };
            assert_eq!(bootstrap.cached_string_literal_type(value), Some(*id));
        }
        for id in [
            bootstrap.boolean_type,
            bootstrap.string_or_number_type,
            bootstrap.string_number_symbol_type,
            bootstrap.number_or_bigint_type,
            bootstrap.template_constraint_type,
            bootstrap.unknown_union_type,
            bootstrap.typeof_type,
        ] {
            assert_eq!(
                bootstrap.cached_union_type(union_types(&store, id)),
                Some(id),
            );
        }
        assert_eq!(
            bootstrap.cached_template_literal_type(
                &[String::new(), String::new()],
                &[bootstrap.number_type],
            ),
            Some(bootstrap.numeric_string_type),
        );
    }

    #[test]
    fn non_strict_bootstrap_preserves_widening_and_nullable_reduction_identity() {
        let store = initialized(IntrinsicBootstrapOptions::default());
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_ne!(bootstrap.undefined_widening_type, bootstrap.undefined_type);
        assert_ne!(bootstrap.null_widening_type, bootstrap.null_type);
        assert_intrinsic(
            &store,
            bootstrap.undefined_widening_type,
            TypeFlags::UNDEFINED,
            "undefined",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        assert_intrinsic(
            &store,
            bootstrap.null_widening_type,
            TypeFlags::NULL,
            "null",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        assert_eq!(
            bootstrap.undefined_or_missing_type,
            bootstrap.undefined_type,
        );
        assert_eq!(bootstrap.unknown_union_type, bootstrap.unknown_type);
        assert_eq!(
            union_types(&store, bootstrap.template_constraint_type),
            [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.regular_false_type,
                bootstrap.regular_true_type,
            ],
        );
        assert_eq!(bootstrap.undefined_widening_type.get(), 11);
        assert_eq!(bootstrap.null_widening_type.get(), 15);
        assert_eq!(bootstrap.empty_generic_type.get(), 42);
        assert_eq!(bootstrap.typeof_type.get(), 63);
        assert_eq!(store.type_len(), 63);
        assert_eq!(bootstrap.union_cache_len(), 6);
        assert_eq!(
            bootstrap.cached_union_type(union_types(&store, bootstrap.template_constraint_type,)),
            Some(bootstrap.template_constraint_type),
        );
        assert_eq!(
            bootstrap.cached_union_type(&[
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ]),
            None,
        );
    }

    #[test]
    fn initialization_is_idempotent_and_rejections_are_atomic() {
        let mut store = TestStore::new();
        let options = IntrinsicBootstrapOptions::default();
        let first = store.initialize_intrinsic_bootstrap(options).unwrap() as *const _;
        let state = checker_state(&store);
        let symbol_count = store.symbol_len();
        let table_count = store.symbol_store().symbol_table_len();
        let second = store.initialize_intrinsic_bootstrap(options).unwrap() as *const _;
        assert_eq!(first, second);
        assert_eq!(checker_state(&store), state);
        assert_eq!(store.symbol_len(), symbol_count);
        assert_eq!(store.symbol_store().symbol_table_len(), table_count);

        let requested = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        };
        assert_eq!(
            store.initialize_intrinsic_bootstrap(requested),
            Err(IntrinsicBootstrapError::OptionsMismatch {
                initialized: options,
                requested,
            }),
        );
        assert_eq!(checker_state(&store), state);
        assert_eq!(store.symbol_len(), symbol_count);
        assert_eq!(store.symbol_store().symbol_table_len(), table_count);

        let mut occupied = TestStore::new();
        let preexisting = occupied
            .alloc_intrinsic_type(TypeFlags::ANY, "preexisting")
            .unwrap();
        let before = checker_state(&occupied);
        assert_eq!(
            occupied.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&occupied), before);
        assert_eq!(occupied.symbol_len(), 0);
        assert_eq!(occupied.symbol_store().symbol_table_len(), 0);
        assert_eq!(
            record(&occupied, preexisting).data(),
            &TypeData::Intrinsic(super::super::type_records::IntrinsicTypeData {
                intrinsic_name: "preexisting".to_owned(),
            }),
        );
        assert!(occupied.intrinsic_bootstrap().is_none());

        let mut mapper_occupied = TestStore::new();
        mapper_occupied
            .new_type_mapper(Vec::new(), Vec::new())
            .unwrap();
        let mut signature_occupied = TestStore::new();
        signature_occupied
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let mut predicate_occupied = TestStore::new();
        predicate_occupied
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "occupied", None)
            .unwrap();
        let mut alias_occupied = TestStore::new();
        alias_occupied.alloc_type_alias(None).unwrap();
        let mut index_occupied = TestStore::new();
        let index_type = index_occupied
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        index_occupied
            .alloc_index_info(index_type, index_type, false, None, Vec::new())
            .unwrap();
        let mut occupied_stores = Vec::with_capacity(5);
        occupied_stores.push(mapper_occupied);
        occupied_stores.push(signature_occupied);
        occupied_stores.push(predicate_occupied);
        occupied_stores.push(alias_occupied);
        occupied_stores.push(index_occupied);
        for mut occupied in occupied_stores {
            let before = checker_state(&occupied);
            let symbol_count = occupied.symbol_len();
            let table_count = occupied.symbol_store().symbol_table_len();
            assert!(!before.is_pristine());
            assert_eq!(
                occupied.initialize_intrinsic_bootstrap(options),
                Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                    before,
                ))),
            );
            assert_eq!(checker_state(&occupied), before);
            assert_eq!(occupied.symbol_len(), symbol_count);
            assert_eq!(occupied.symbol_store().symbol_table_len(), table_count);
            assert!(occupied.intrinsic_bootstrap().is_none());
        }
    }

    #[test]
    fn prebound_binder_symbols_and_tables_are_allowed_and_preserved() {
        let mut symbols = SymbolStore::new();
        let bound_symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::CLASS,
                EscapedName::source("bound"),
            ))
            .unwrap();
        let private_name = symbols
            .private_identifier_name(bound_symbol, "#field")
            .unwrap();
        assert!(private_name.as_ref().is_private_identifier());
        let bound_global_id = symbols.global_symbol_id(bound_symbol).unwrap();
        let bound_table = symbols.alloc_symbol_table();
        assert_eq!(
            symbols.insert_symbol(bound_table, EscapedName::source("bound"), bound_symbol,),
            Some(None),
        );
        let mut store = TestStore::from_symbol_store(symbols);
        let parsed = parse_source_file("const prebound = 1;");
        assert!(store.register_ast_scope(AstScope::new(FileId::new(0), &parsed.arena,)));

        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        assert_eq!(store.global_symbol_id(bound_symbol), Some(bound_global_id));
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(bootstrap.undefined_symbol.get(), bound_symbol.get() + 1);
        assert_eq!(bootstrap.globals.get(), bound_table.get() + 1);
        assert_eq!(
            store.symbol(bound_symbol).unwrap().name().as_utf8(),
            Some("bound"),
        );
        assert_eq!(
            store.symbol_table(bound_table).unwrap().get_source("bound"),
            Some(bound_symbol),
        );
        assert_eq!(
            store
                .symbol_table(bootstrap.globals)
                .unwrap()
                .get_source("globalThis"),
            Some(bootstrap.global_this_symbol),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exercises every disjoint checker-owned side store.
    fn sparse_links_and_resolution_state_reject_bootstrap_atomically() {
        let options = IntrinsicBootstrapOptions::default();
        let parsed = parse_source_file(
            "enum E { A } const asserted = value as string; const array = [...items]; \
             switch (value) { case 0: break; } factory();",
        );
        let file = FileId::new(0);
        let mut symbols = SymbolStore::new();
        let linked_symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("linked"),
            ))
            .unwrap();
        let mut linked = TestStore::from_symbol_store(symbols);
        let source_file = linked
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let node = source_file.node_ref();
        let node_of_kind = |kind| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(id, node)| (node.kind == kind).then_some(id))
                .unwrap_or_else(|| panic!("parsed source must contain {kind:?}"));
            NodeRef::new(parsed.arena.id(), file, node)
        };
        assert!(linked.register_entity_name_text("factory").is_some());
        assert!(linked.ensure_node_links(node));
        assert!(linked.ensure_symbol_node_links(node));
        assert!(linked.ensure_type_node_links(node));
        assert!(linked.ensure_enum_member_links(node_of_kind(SyntaxKind::EnumMember)));
        assert!(linked.ensure_assertion_links(node_of_kind(SyntaxKind::AsExpression)));
        assert!(
            linked.ensure_array_literal_links(node_of_kind(SyntaxKind::ArrayLiteralExpression))
        );
        assert!(linked.ensure_switch_statement_links(node_of_kind(SyntaxKind::SwitchStatement)));
        assert!(linked.ensure_jsx_element_links(node));
        assert!(linked.ensure_signature_links(node_of_kind(SyntaxKind::CallExpression)));
        assert!(linked.ensure_symbol_reference_links(linked_symbol));
        assert!(linked.ensure_value_symbol_links(linked_symbol));
        assert!(linked.ensure_mapped_symbol_links(linked_symbol));
        assert!(linked.ensure_deferred_symbol_links(linked_symbol));
        assert!(linked.ensure_alias_symbol_links(linked_symbol));
        assert!(linked.ensure_module_symbol_links(linked_symbol));
        assert!(linked.ensure_late_bound_links(linked_symbol));
        assert!(linked.ensure_export_type_links(linked_symbol));
        assert!(linked.ensure_members_and_exports_links(linked_symbol));
        assert!(linked.ensure_type_alias_links(linked_symbol));
        assert!(linked.ensure_declared_type_links(linked_symbol));
        assert!(linked.ensure_spread_links(linked_symbol));
        assert!(linked.ensure_variance_links(linked_symbol));
        assert!(linked.ensure_reverse_mapped_symbol_links(linked_symbol));
        assert!(linked.ensure_marked_assignment_symbol_links(linked_symbol));
        assert!(linked.ensure_containing_symbol_links(linked_symbol));
        assert!(linked.ensure_source_file_links(source_file));
        let before = checker_state(&linked);
        assert_eq!(before.semantic_arenas.entity_names, 1);
        assert_eq!(
            before.links,
            CheckerLinkCounts {
                node: 1,
                symbol_node: 1,
                type_node: 1,
                enum_member: 1,
                assertion: 1,
                array_literal: 1,
                switch_statement: 1,
                jsx_element: 1,
                signature: 1,
                symbol_reference: 1,
                value_symbol: 1,
                mapped_symbol: 1,
                deferred_symbol: 1,
                alias_symbol: 1,
                module_symbol: 1,
                late_bound: 1,
                export_type: 1,
                members_and_exports: 1,
                type_alias: 1,
                declared_type: 1,
                spread: 1,
                variance: 1,
                reverse_mapped_symbol: 1,
                marked_assignment_symbol: 1,
                containing_symbol: 1,
                source_file: 1,
            },
        );
        assert_eq!(
            linked.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&linked), before);
        assert!(linked.node_links(node).is_some());
        assert_eq!(linked.symbol_len(), 1);
        assert_eq!(linked.symbol_store().symbol_table_len(), 0);

        let mut symbols = SymbolStore::new();
        let symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("resolving"),
            ))
            .unwrap();
        let mut resolving = TestStore::from_symbol_store(symbols);
        assert_eq!(
            resolving.push_type_resolution(
                crate::semantic::TypeResolutionTarget::Symbol(symbol),
                crate::semantic::TypeSystemPropertyName::Type,
            ),
            Ok(true),
        );
        let before = checker_state(&resolving);
        assert_eq!(before.type_resolution.entries, 1);
        assert_eq!(
            resolving.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&resolving), before);
        assert_eq!(resolving.pop_type_resolution(), Some(true));

        let mut bounded = TestStore::new();
        let boundary = bounded.reset_type_resolution_start();
        let before = checker_state(&bounded);
        assert_eq!(before.type_resolution.boundaries, 1);
        assert_eq!(before.type_resolution.next_boundary_serial, 1);
        assert_eq!(
            bounded.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&bounded), before);
        assert!(bounded.restore_type_resolution_start(boundary).is_ok());

        let mut boundary_history = TestStore::new();
        let boundary = boundary_history.reset_type_resolution_start();
        assert!(
            boundary_history
                .restore_type_resolution_start(boundary)
                .is_ok(),
        );
        let before = checker_state(&boundary_history);
        assert_eq!(before.type_resolution.boundaries, 0);
        assert_eq!(before.type_resolution.next_boundary_serial, 1);
        assert_eq!(
            boundary_history.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&boundary_history), before);

        let mut symbols = SymbolStore::new();
        let enum_source = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::REGULAR_ENUM,
                EscapedName::source("Source"),
            ))
            .unwrap();
        let enum_target = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::REGULAR_ENUM,
                EscapedName::source("Target"),
            ))
            .unwrap();
        let mut related = TestStore::from_symbol_store(symbols);
        let relation_key = crate::semantic::CacheHashKey::from_halves(1, 2);
        for relation in crate::semantic::RelationKind::ALL {
            related.relation_cache_set(
                relation,
                relation_key,
                crate::semantic::RelationComparisonResult::SUCCEEDED,
            );
        }
        assert!(related.enum_relation_cache_set(
            enum_source,
            enum_target,
            crate::semantic::RelationComparisonResult::FAILED,
        ));
        let before = checker_state(&related);
        assert_eq!(before.relations.subtype.entries, 1);
        assert_eq!(before.relations.strict_subtype.entries, 1);
        assert_eq!(before.relations.assignable.entries, 1);
        assert_eq!(before.relations.comparable.entries, 1);
        assert_eq!(before.relations.identity.entries, 1);
        assert_eq!(before.relations.enum_relation_entries, 1);
        assert_eq!(
            related.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&related), before);
        for relation in crate::semantic::RelationKind::ALL {
            assert_eq!(
                related.relation_cache_get(relation, relation_key),
                crate::semantic::RelationComparisonResult::SUCCEEDED
            );
        }
        assert_eq!(
            related.enum_relation_cache_get(enum_source, enum_target),
            Some(crate::semantic::RelationComparisonResult::FAILED)
        );

        let mut symbols = SymbolStore::new();
        let _ = symbols.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("premature"),
            CheckFlags::NONE,
        );
        let mut transient = TestStore::from_symbol_store(symbols);
        let before = checker_state(&transient);
        assert_eq!(before.checker_symbols, 1);
        assert_eq!(
            transient.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&transient), before);
    }

    #[test]
    fn every_bootstrap_handle_is_store_branded() {
        let first = initialized(IntrinsicBootstrapOptions::default());
        let first_bootstrap = first.intrinsic_bootstrap().unwrap();
        let any_type = first_bootstrap.any_type;
        let global_this_symbol = first_bootstrap.global_this_symbol;
        let globals = first_bootstrap.globals;
        let predicate = first_bootstrap.no_type_predicate;
        let signature = first_bootstrap.any_signature;
        let index_info = first_bootstrap.enum_number_index_info;
        let boolean_constituents = union_types(&first, first_bootstrap.boolean_type).to_vec();
        let number_type = first_bootstrap.number_type;

        let second = initialized(IntrinsicBootstrapOptions::default());
        let second_bootstrap = second.intrinsic_bootstrap().unwrap();
        assert_eq!(any_type.get(), second_bootstrap.any_type.get());
        assert_ne!(any_type, second_bootstrap.any_type);
        assert!(second.type_payload(any_type).is_none());
        assert!(second.symbol(global_this_symbol).is_none());
        assert!(second.symbol_table(globals).is_none());
        assert!(second.type_predicate(predicate).is_none());
        assert!(second.signature(signature).is_none());
        assert!(second.index_info(index_info).is_none());
        assert_eq!(
            second_bootstrap.cached_union_type(&boolean_constituents),
            None,
        );
        assert_eq!(
            second_bootstrap
                .cached_template_literal_type(&[String::new(), String::new()], &[number_type],),
            None,
        );
    }
}
