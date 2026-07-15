//! Dependency-closed canonical semantic type display.
//!
//! This is the primitive and literal prefix of pinned
//! `internal/checker/printer.go::typeToString`,
//! `internal/checker/nodebuilderimpl.go::typeToTypeNode`, and
//! `internal/checker/relater.go::reportRelationError` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. It deliberately stops before
//! symbol naming, alias accessibility, and general union serialization. Those
//! families return [`TypeDisplayUnavailable`] rather than placeholder text.

use std::{fmt::Write as _, ops};

use super::{
    CanonicalTypeMapperStore, TypeAliasId, TypeId,
    type_records::{LiteralTypeData, LiteralValue, TypeData, TypeDataKind, TypeRecord},
    types::TypeFlags,
};

const DEFAULT_MAXIMUM_TRUNCATION_LENGTH: usize = 160;
const NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH: usize = 1_000_000;
const ELLIPSIS: &str = "...";

/// The pinned `TypeFormatFlags` subset observable for dependency-closed
/// primitive and literal display.
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
    /// Alias naming itself remains an explicit dependency boundary in this cut.
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

/// A canonical type or display dependency outside the installed formatter
/// prefix. No variant contains substitute display text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeDisplayUnavailable {
    Type(TypeId),
    Alias { type_id: TypeId, alias: TypeAliasId },
    UnsupportedType { type_id: TypeId, kind: TypeDataKind },
    MalformedType(TypeId),
    InvalidLiteralLinks(TypeId),
    InvalidNumberLiteral(TypeId),
    UniqueSymbolName(TypeId),
    MissingBootstrap,
    FullyQualifiedName { source: TypeId, target: TypeId },
    Utf8TruncationBoundary { type_id: TypeId, boundary: usize },
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
            Self::InvalidLiteralLinks(type_id) => write!(
                formatter,
                "literal type {type_id:?} has invalid fresh/regular links"
            ),
            Self::InvalidNumberLiteral(type_id) => write!(
                formatter,
                "number literal type {type_id:?} has no source-literal spelling"
            ),
            Self::UniqueSymbolName(type_id) => write!(
                formatter,
                "unique symbol type {type_id:?} requires symbol-aware display"
            ),
            Self::MissingBootstrap => {
                formatter.write_str("literal relation display requires intrinsic checker bootstrap")
            }
            Self::FullyQualifiedName { source, target } => write!(
                formatter,
                "types {source:?} and {target:?} require symbol-aware fully qualified display"
            ),
            Self::Utf8TruncationBoundary { type_id, boundary } => write!(
                formatter,
                "pinned byte truncation for {type_id:?} splits UTF-8 at byte {boundary}"
            ),
        }
    }
}

impl std::error::Error for TypeDisplayUnavailable {}

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
/// installed primitive/literal prefix.
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
    let displayed = display_type_worker(store, type_id, flags)?;
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
    let flags = flags | CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    let source_record = store
        .type_payload(source)
        .ok_or(TypeDisplayUnavailable::Type(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(TypeDisplayUnavailable::Type(target))?;
    let mut source_name = type_to_string_with_flags(store, source, flags)?;
    let target_name = type_to_string_with_flags(store, target, flags)?;

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
        && !type_could_have_top_level_singleton_types(target_record)
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
        source_name = type_to_string_with_flags(store, generalized, flags)?;
    }

    Ok(AssignabilityErrorDisplay {
        source: source_name,
        target: target_name,
    })
}

fn display_type_worker(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<String, TypeDisplayUnavailable> {
    let record = store
        .type_payload(type_id)
        .ok_or(TypeDisplayUnavailable::Type(type_id))?;
    let type_flags = record.flags();

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
                return Ok("intrinsic".to_owned());
            }
        }
        return Ok("any".to_owned());
    }
    if type_flags.intersects(TypeFlags::UNKNOWN) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("unknown".to_owned());
    }
    if type_flags.intersects(TypeFlags::STRING) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("string".to_owned());
    }
    if type_flags.intersects(TypeFlags::NUMBER) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("number".to_owned());
    }
    if type_flags.intersects(TypeFlags::BIG_INT) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("bigint".to_owned());
    }
    if type_flags.intersects(TypeFlags::BOOLEAN) {
        if let Some(alias) = record.alias() {
            return Err(TypeDisplayUnavailable::Alias { type_id, alias });
        }
        require_data_kind(type_id, record, TypeDataKind::Union)?;
        return Ok("boolean".to_owned());
    }
    if type_flags.intersects(TypeFlags::ENUM_LIKE) {
        return Err(TypeDisplayUnavailable::UnsupportedType {
            type_id,
            kind: record.data().kind(),
        });
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
        return Ok(quote_string_literal(value, quote));
    }
    if type_flags.intersects(TypeFlags::NUMBER_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::Number(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        if value.is_nan() {
            return Err(TypeDisplayUnavailable::InvalidNumberLiteral(type_id));
        }
        return Ok(value.to_string());
    }
    if type_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::BigInt(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        return Ok(format!("{value}n"));
    }
    if type_flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        let literal = literal_data(type_id, record)?;
        validate_literal_links(store, type_id, record, literal)?;
        let LiteralValue::Boolean(value) = &literal.value else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        return Ok(value.to_string());
    }
    if type_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
        require_data_kind(type_id, record, TypeDataKind::UniqueEsSymbol)?;
        if !flags.contains(CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE) {
            return Err(TypeDisplayUnavailable::UniqueSymbolName(type_id));
        }
        return Ok("unique symbol".to_owned());
    }
    if type_flags.intersects(TypeFlags::VOID) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("void".to_owned());
    }
    if type_flags.intersects(TypeFlags::UNDEFINED) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("undefined".to_owned());
    }
    if type_flags.intersects(TypeFlags::NULL) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("null".to_owned());
    }
    if type_flags.intersects(TypeFlags::NEVER) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("never".to_owned());
    }
    if type_flags.intersects(TypeFlags::ES_SYMBOL) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("symbol".to_owned());
    }
    if type_flags.intersects(TypeFlags::NON_PRIMITIVE) {
        require_data_kind(type_id, record, TypeDataKind::Intrinsic)?;
        return Ok("object".to_owned());
    }
    if let Some(alias) = record.alias() {
        return Err(TypeDisplayUnavailable::Alias { type_id, alias });
    }
    Err(TypeDisplayUnavailable::UnsupportedType {
        type_id,
        kind: record.data().kind(),
    })
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

fn type_could_have_top_level_singleton_types(record: &TypeRecord) -> bool {
    // Pinned behavior intentionally treats `boolean` as non-singleton even
    // though its representation is `false | true`.
    !record.flags().intersects(TypeFlags::BOOLEAN) && record.flags().intersects(TypeFlags::UNIT)
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
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        type_records::{LiteralValue, RegularLiteralLink},
    };

    fn bootstrapped_store() -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::default();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
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
        let (any_type, boolean_type, string_type) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                (
                    bootstrap.any_type,
                    bootstrap.boolean_type,
                    bootstrap.string_type,
                )
            })
            .unwrap();
        let literal_type = store.regular_string_literal_type("value".into()).unwrap();

        let any_alias = attach_type_alias(&mut store, any_type, "AnyAlias");
        let boolean_alias = attach_type_alias(&mut store, boolean_type, "BooleanAlias");
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
            type_to_string(&store, boolean_type),
            Err(TypeDisplayUnavailable::Alias {
                type_id: boolean_type,
                alias: boolean_alias,
            })
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
    fn canonicalizes_signed_zero_and_rejects_nan() {
        let mut store = bootstrapped_store();
        let negative_zero = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(-0.0)),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        assert_eq!(type_to_string(&store, negative_zero).unwrap(), "0");

        let nan = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::nan()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        assert_eq!(
            type_to_string(&store, nan),
            Err(TypeDisplayUnavailable::InvalidNumberLiteral(nan))
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
    fn unique_symbol_is_flag_gated_and_general_unions_are_unavailable() {
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
            Err(TypeDisplayUnavailable::UnsupportedType {
                type_id: union,
                kind: TypeDataKind::Union,
            })
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
