use std::collections::{BTreeMap, HashMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    SemanticSymbolId, SymbolFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalTypeMapperStore,
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable, TypeId, TypeResolutionTarget,
    TypeSystemPropertyName, UnsupportedDeclaredTypeKind,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    declared::{
        cached_ordinary_type_parameter_owner, execute_type_parameter,
        explicit_type_parameter_symbols, get_declared_class_interface_or_type_parameter,
        malformed_alias_merge, preflight_class_or_interface_reference, preflight_node,
        preflight_type_parameter_symbol, type_list_key,
    },
    type_records::{TypeData, TypeRecord},
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
    type_parameter_symbols: Vec<SemanticSymbolId>,
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
    aliases: BTreeMap<SemanticSymbolId, TypeAliasPlan>,
    references: BTreeMap<NodeRef, SemanticSymbolId>,
    literals: BTreeMap<NodeRef, PlannedLiteralType>,
    unions: BTreeMap<NodeRef, PlannedUnionType>,
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
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CachedTypeAliasRhs {
    DirectUnion,
    TypeReference(NodeRef),
    NonUnion,
}

fn type_node_unavailable(reason: TypeNodeUnavailable) -> DeclaredTypeError {
    DeclaredTypeError::TypeNodeUnavailable(reason)
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
    symbol: SemanticSymbolId,
    strict_builtin_iterator_return: bool,
) -> Result<Option<CachedTypeAlias>, DeclaredTypeError> {
    let Some(links) = store.type_alias_links(symbol) else {
        return Ok(None);
    };
    let Some(declared_type) = links.declared_type else {
        if links.type_parameters.is_some() || links.instantiations.is_some() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        return Ok(None);
    };

    let type_parameter_count = match links.type_parameters.as_deref() {
        None if links.instantiations.is_none() => 0,
        Some(type_parameters) if !type_parameters.is_empty() => {
            let unique_parameters = type_parameters.iter().copied().collect::<HashSet<_>>();
            let parameters_are_valid = unique_parameters.len() == type_parameters.len()
                && type_parameters.iter().all(|parameter| {
                    cached_ordinary_type_parameter_owner(store, *parameter).is_some()
                });
            let has_identity_seed = links.instantiations.as_ref().is_some_and(|instantiations| {
                instantiations
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
    }))
}

struct TypeQueryPlanner<'store, 'host, 'arena> {
    store: &'store CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    strict_builtin_iterator_return: bool,
    plan: TypeQueryPlan,
}

impl<'store, 'host, 'arena> TypeQueryPlanner<'store, 'host, 'arena> {
    fn new(
        store: &'store CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        strict_builtin_iterator_return: bool,
    ) -> Self {
        Self {
            store,
            host,
            strict_builtin_iterator_return,
            plan: TypeQueryPlan::default(),
        }
    }

    fn finish(self) -> TypeQueryPlan {
        self.plan
    }

    fn plan_type_node(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        self.plan_type_node_in_context(node, None, false)
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
        if let Some(cached) = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        {
            if record.kind == SyntaxKind::UnionType {
                let derived_alias = self.direct_union_alias(node)?;
                if alias_owner.is_some() && derived_alias != alias_owner {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidUnionType(node),
                    ));
                }
                self.store
                    .validate_cached_union_result(cached, alias_owner.or(derived_alias))
                    .map_err(type_construction_error)?;
                return Ok(());
            }
            if union_constituent {
                self.store
                    .validate_cached_union_result(cached, None)
                    .map_err(type_construction_error)?;
            }
        }
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
            SyntaxKind::TypeReference => self.plan_type_reference(node, union_constituent),
            SyntaxKind::UnionType => self.plan_union_type(node, alias_owner),
            kind if union_constituent => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(node),
            )),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
        }
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
        if union_constituent
            || matches!(
                declared_data,
                Some(TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::Union(_))
            )
        {
            self.store
                .validate_cached_union_result(declared_type, None)
                .map_err(type_construction_error)?;
        }

        let mut symbol = root_symbol;
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(symbol) {
                if remains_union {
                    return Err(type_construction_error(
                        LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                    ));
                }
                let is_canonical_cycle_error = self
                    .store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| declared_type == bootstrap.error_type);
                return if is_canonical_cycle_error {
                    Ok(())
                } else {
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                    ))
                };
            }
            let has_host_declaration = self
                .store
                .symbol(symbol)
                .and_then(|symbol| symbol.declarations())
                .and_then(|declarations| declarations.first())
                .is_some_and(|declaration| self.host.source(*declaration).is_some());
            if !has_host_declaration {
                // Fully cached queries intentionally support an empty host.
                // The canonical semantic identity was validated above; AST
                // RHS provenance is enforced whenever its owner is available.
                return Ok(());
            }
            match self.cached_type_alias_rhs(symbol)? {
                CachedTypeAliasRhs::DirectUnion => {
                    if remains_union {
                        self.store
                            .validate_cached_union_result(declared_type, Some(symbol))
                            .map_err(type_construction_error)?;
                    }
                    return Ok(());
                }
                CachedTypeAliasRhs::NonUnion => {
                    if remains_union {
                        return Err(type_construction_error(
                            LiteralTypeCacheError::InvalidCachedUnion(declared_type),
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
                    let flags = self
                        .store
                        .symbol(canonical)
                        .map(ts_binder::semantic::Symbol::flags)
                        .ok_or(DeclaredTypeError::Unavailable(
                            DeclaredTypeUnavailable::SymbolNotOwned(canonical),
                        ))?;
                    if !flags.contains(SymbolFlags::TYPE_ALIAS) || malformed_alias_merge(flags) {
                        if remains_union {
                            return Err(type_construction_error(
                                LiteralTypeCacheError::InvalidCachedUnion(declared_type),
                            ));
                        }
                        return Ok(());
                    }
                    let Some(target_cached) = cached_type_alias(
                        self.store,
                        canonical,
                        self.strict_builtin_iterator_return,
                    )?
                    else {
                        return Err(type_node_unavailable(
                            TypeNodeUnavailable::InvalidCachedTypeAlias(root_symbol),
                        ));
                    };
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
        union_constituent: bool,
    ) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::TypeReferenceNode(reference) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        if reference
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.nodes.is_empty())
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(node),
            ));
        }

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

        if !union_constituent
            && self
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .is_some()
        {
            return Ok(());
        }

        let symbol = if let Some(symbol) = self
            .store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        {
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

        if union_constituent && !flags.contains(SymbolFlags::TYPE_ALIAS) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedUnionConstituent(node),
            ));
        }

        if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            let local_count =
                preflight_class_or_interface_reference(self.store, self.host, symbol, flags)?;
            if local_count != 0 {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
                ));
            }
        } else if flags.contains(SymbolFlags::TYPE_PARAMETER) {
            preflight_type_parameter_symbol(self.store, self.host, symbol, &mut HashSet::new())?;
        } else if flags.contains(SymbolFlags::TYPE_ALIAS) {
            let type_parameter_count = self.plan_type_alias(symbol, union_constituent)?;
            if type_parameter_count != 0 {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
                ));
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
        }

        if let Some(existing) = self.plan.references.insert(node, symbol) {
            assert_eq!(existing, symbol, "one type-reference node has one symbol");
        }
        Ok(())
    }

    fn plan_type_alias(
        &mut self,
        symbol: SemanticSymbolId,
        union_constituent: bool,
    ) -> Result<usize, DeclaredTypeError> {
        if let Some(cached) =
            cached_type_alias(self.store, symbol, self.strict_builtin_iterator_return)?
        {
            self.validate_cached_type_alias_identity(symbol, cached, union_constituent)?;
            return Ok(cached.type_parameter_count);
        }
        if let Some(plan) = self.plan.aliases.get(&symbol) {
            return Ok(plan.type_parameter_symbols.len());
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

        let mut first = None;
        let mut type_parameter_symbols = Vec::new();
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
            for parameter in explicit_type_parameter_symbols(
                self.store,
                self.host,
                declaration,
                alias.type_parameters.as_ref(),
                &mut checked,
            )? {
                if !type_parameter_symbols.contains(&parameter) {
                    type_parameter_symbols.push(parameter);
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
        let type_parameter_count = type_parameter_symbols.len();
        self.plan.aliases.insert(
            symbol,
            TypeAliasPlan {
                name,
                name_text,
                type_node,
                type_parameter_symbols,
            },
        );
        self.plan_type_node_in_context(type_node, Some(symbol), union_constituent)?;
        Ok(type_parameter_count)
    }
}

pub(super) struct CanonicalTypeQuery<'store, 'host, 'arena, 'diagnostics> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    options: CanonicalTypeQueryOptions,
    diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
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
            options,
            diagnostics,
        })
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
        let mut planner = TypeQueryPlanner::new(
            self.store,
            self.host,
            self.options.strict_builtin_iterator_return,
        );
        planner.plan_type_node(node)?;
        let plan = planner.finish();
        let mut prepared = self.prepare_literal_types(&plan)?;
        self.execute_type_node(node, &plan, &mut prepared)
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
            self.options.strict_builtin_iterator_return,
        );
        if !flags
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::TYPE_PARAMETER)
            && flags.contains(SymbolFlags::TYPE_ALIAS)
        {
            planner.plan_type_alias(symbol, false)?;
        }
        let plan = planner.finish();
        let mut prepared = self.prepare_literal_types(&plan)?;
        self.execute_declared_type(symbol, &plan, &mut prepared)
    }

    fn prepare_literal_types(
        &mut self,
        plan: &TypeQueryPlan,
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
        let named_unions = unions
            .iter()
            .filter(|union| union.alias_symbol.is_some())
            .count();
        self.store
            .prepare_type_query_types(&strings, &numbers, &bigints, unions.len(), named_unions)
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

    fn execute_type_alias(
        &mut self,
        symbol: SemanticSymbolId,
        plan: &TypeQueryPlan,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(cached) = cached_type_alias(
            self.store,
            symbol,
            self.options.strict_builtin_iterator_return,
        )? {
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
            if !alias.type_parameter_symbols.is_empty() {
                let type_parameters = alias
                    .type_parameter_symbols
                    .iter()
                    .map(|parameter| execute_type_parameter(self.store, *parameter))
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
            SyntaxKind::TypeReference => self.execute_type_reference(node, plan, prepared),
            SyntaxKind::UnionType => self.execute_union_type(node, plan, prepared),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
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
        let resolved_type = self
            .store
            .literal_union_type_prepared(&types, union.alias_symbol, prepared)
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
        if let Some(resolved_type) = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        {
            return Ok(resolved_type);
        }
        let symbol = plan.references.get(&node).copied().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeReference(node))
        })?;

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
            if cached != canonical {
                symbol_links.resolved_symbol = Some(canonical);
                if !self.store.set_symbol_node_links(node, symbol_links.clone()) {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidCachedSymbol {
                            node,
                            symbol: cached,
                        },
                    ));
                }
            }
        } else {
            symbol_links.resolved_symbol = Some(symbol);
            if !self.store.set_symbol_node_links(node, symbol_links) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedSymbol { node, symbol },
                ));
            }
        }

        let resolved_type = self.execute_declared_type(symbol, plan, prepared)?;
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
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeHostError, DeclaredTypeLinks, IntrinsicBootstrapOptions, SymbolNodeLinks,
        TypeAliasLinks, TypeNodeLinks,
        production::GlobalMergeCompletion,
        type_records::LiteralValue,
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

    fn store_state(store: &CanonicalTypeMapperStore) -> StoreState {
        (
            store.type_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.type_resolution_len(),
            store.type_resolution_start(),
        )
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
            ("type Id<T> = T; type Bad = Id;", 3),
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
            "type ObjectAlias = { value: string }; type FunctionAlias = () => string; ",
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
            "ObjectAlias",
            "FunctionAlias",
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
}
