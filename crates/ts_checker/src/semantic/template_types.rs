//! Canonical template-literal construction and intrinsic string mappings.
//!
//! The algorithms follow `getTemplateLiteralType`, `getStringMappingType`,
//! and `checkCrossProductUnion` in the pinned upstream checker.

use std::{cmp::Ordering, collections::HashSet, fmt};

use ts_ast::{append_js_string, decode_js_string, encode_js_string};
use ts_binder::SemanticSymbolId;
use ts_jsnum::Number;

use super::{
    CanonicalTypeMapperStore, TypeId,
    bootstrap::LiteralTypeCacheError,
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// Upstream rejects a union cross product when it reaches this size.
pub const MAX_TEMPLATE_UNION_SIZE: usize = 100_000;

/// Intrinsic string operations supported by the standard library.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StringMappingKind {
    Uppercase,
    Lowercase,
    Capitalize,
    Uncapitalize,
}

impl StringMappingKind {
    /// Resolves an intrinsic operation from its declaration name.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Uppercase" => Some(Self::Uppercase),
            "Lowercase" => Some(Self::Lowercase),
            "Capitalize" => Some(Self::Capitalize),
            "Uncapitalize" => Some(Self::Uncapitalize),
            _ => None,
        }
    }

    /// Applies JavaScript-style Unicode case conversion to one string.
    #[must_use]
    pub fn apply(self, value: &str) -> String {
        match self {
            Self::Uppercase => javascript_uppercase(value),
            Self::Lowercase => javascript_lowercase(value),
            Self::Capitalize | Self::Uncapitalize => {
                let Some((first, rest)) = split_first_template_code_point(value) else {
                    return String::new();
                };
                let mut result = match self {
                    Self::Capitalize => javascript_uppercase(first),
                    Self::Uncapitalize => javascript_lowercase(first),
                    Self::Uppercase | Self::Lowercase => unreachable!(),
                };
                result.push_str(rest);
                result
            }
        }
    }
}

/// Splits one encoded JavaScript code point without separating a lone surrogate.
pub(super) fn split_first_template_code_point(value: &str) -> Option<(&str, &str)> {
    let mut characters = value.char_indices();
    let (_, first) = characters.next()?;
    let mut boundary = first.len_utf8();
    if first == '\u{10fffd}'
        && let Some((offset, second)) = characters.next()
    {
        let candidate_end = offset + second.len_utf8();
        let candidate = &value[..candidate_end];
        if encode_js_string(&decode_js_string(candidate)) == candidate {
            boundary = candidate_end;
        }
    }
    Some(value.split_at(boundary))
}

fn valid_bigint_template_fragment(value: &str) -> bool {
    let unsigned = value.strip_prefix('-').unwrap_or(value);
    if unsigned.is_empty() {
        return false;
    }
    let (digits, radix) = if let Some(digits) = unsigned
        .strip_prefix("0x")
        .or_else(|| unsigned.strip_prefix("0X"))
    {
        (digits, 16)
    } else if let Some(digits) = unsigned
        .strip_prefix("0o")
        .or_else(|| unsigned.strip_prefix("0O"))
    {
        (digits, 8)
    } else if let Some(digits) = unsigned
        .strip_prefix("0b")
        .or_else(|| unsigned.strip_prefix("0B"))
    {
        (digits, 2)
    } else {
        if unsigned.len() > 1 && unsigned.starts_with('0') {
            return false;
        }
        (unsigned, 10)
    };
    !digits.is_empty()
        && digits.bytes().all(|digit| match radix {
            2 => matches!(digit, b'0' | b'1'),
            8 => matches!(digit, b'0'..=b'7'),
            16 => digit.is_ascii_hexdigit(),
            _ => digit.is_ascii_digit(),
        })
}

fn javascript_uppercase(value: &str) -> String {
    let mut result = String::with_capacity(value.len());
    for character in value.chars() {
        if has_post_unicode_15_case_mapping(character) {
            result.push(character);
        } else {
            result.extend(character.to_uppercase());
        }
    }
    result
}

fn javascript_lowercase(value: &str) -> String {
    let mut result = String::with_capacity(value.len());
    let mut start = 0;
    for (index, character) in value.char_indices() {
        if has_post_unicode_15_case_mapping(character)
            && !matches!(character, '\u{019B}' | '\u{0264}' | '\u{A7D3}' | '\u{A7D5}')
        {
            result.push_str(&value[start..index].to_lowercase());
            result.push(character);
            start = index + character.len_utf8();
        }
    }
    result.push_str(&value[start..].to_lowercase());
    result
}

fn has_post_unicode_15_case_mapping(character: char) -> bool {
    matches!(
        character,
        '\u{019B}'
            | '\u{0264}'
            | '\u{1C89}'
            | '\u{1C8A}'
            | '\u{A7CB}'
            | '\u{A7CC}'
            | '\u{A7CD}'
            | '\u{A7CE}'
            | '\u{A7CF}'
            | '\u{A7D2}'
            | '\u{A7D3}'
            | '\u{A7D4}'
            | '\u{A7D5}'
            | '\u{A7DA}'
            | '\u{A7DB}'
            | '\u{A7DC}'
            | '\u{10D50}'..='\u{10D65}'
            | '\u{10D70}'..='\u{10D85}'
            | '\u{16EA0}'..='\u{16EB8}'
            | '\u{16EBB}'..='\u{16ED3}'
    )
}

/// A malformed type, unavailable cache, or excessive template expansion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TemplateTypeError {
    BootstrapUninitialized,
    InvalidShape {
        text_count: usize,
        type_count: usize,
    },
    InvalidType(TypeId),
    InvalidTemplate(TypeId),
    InvalidUnion(TypeId),
    InvalidLiteral(TypeId),
    InvalidMappingSymbol(SemanticSymbolId),
    UnsupportedMappingSymbol(SemanticSymbolId),
    UnsupportedUnionConstituent(TypeId),
    CrossProductTooLarge {
        size: usize,
        limit: usize,
    },
    RecursiveType(TypeId),
    Capacity,
}

impl fmt::Display for TemplateTypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("template types require intrinsic checker bootstrap")
            }
            Self::InvalidShape {
                text_count,
                type_count,
            } => write!(
                formatter,
                "template has {text_count} text segments for {type_count} substitutions"
            ),
            Self::InvalidType(type_) => write!(formatter, "type {type_:?} is not store-owned"),
            Self::InvalidTemplate(type_) => {
                write!(formatter, "template type {type_:?} is malformed")
            }
            Self::InvalidUnion(type_) => write!(formatter, "union type {type_:?} is malformed"),
            Self::InvalidLiteral(type_) => {
                write!(formatter, "literal type {type_:?} is malformed")
            }
            Self::InvalidMappingSymbol(symbol) => {
                write!(formatter, "mapping symbol {symbol:?} is not store-owned")
            }
            Self::UnsupportedMappingSymbol(symbol) => {
                write!(
                    formatter,
                    "mapping symbol {symbol:?} is not a string intrinsic"
                )
            }
            Self::UnsupportedUnionConstituent(type_) => {
                write!(formatter, "union constituent {type_:?} is unsupported")
            }
            Self::CrossProductTooLarge { size, limit } => {
                write!(
                    formatter,
                    "template union size {size} reached the limit {limit}"
                )
            }
            Self::RecursiveType(type_) => {
                write!(
                    formatter,
                    "template type {type_:?} contains a recursive edge"
                )
            }
            Self::Capacity => formatter.write_str("template type capacity was exhausted"),
        }
    }
}

impl std::error::Error for TemplateTypeError {}

impl From<LiteralTypeCacheError> for TemplateTypeError {
    fn from(error: LiteralTypeCacheError) -> Self {
        match error {
            LiteralTypeCacheError::BootstrapUninitialized => Self::BootstrapUninitialized,
            LiteralTypeCacheError::InvalidCachedLiteral(type_) => Self::InvalidLiteral(type_),
            LiteralTypeCacheError::InvalidCachedUnion(type_) => Self::InvalidUnion(type_),
            LiteralTypeCacheError::UnsupportedUnionConstituent(type_)
            | LiteralTypeCacheError::ArrayType { type_, .. } => {
                Self::UnsupportedUnionConstituent(type_)
            }
            LiteralTypeCacheError::InvalidUnionAlias(symbol) => Self::InvalidMappingSymbol(symbol),
            LiteralTypeCacheError::InvalidValue
            | LiteralTypeCacheError::InvalidPreparedQuery
            | LiteralTypeCacheError::Capacity => Self::Capacity,
        }
    }
}

#[derive(Default)]
struct NormalizedTemplate {
    current: String,
    texts: Vec<String>,
    types: Vec<TypeId>,
}

enum TemplateUnionPlan {
    Existing(TypeId),
    Constituents(Vec<TypeId>),
}

impl CanonicalTypeMapperStore {
    /// Returns the canonical type of a template and distributes union spans.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or foreign substitutions, an unavailable
    /// checker bootstrap, an excessive union cross product, or allocation failure.
    pub fn get_template_literal_type(
        &mut self,
        texts: &[String],
        types: &[TypeId],
    ) -> Result<TypeId, TemplateTypeError> {
        if texts.len() != types.len().saturating_add(1) {
            return Err(TemplateTypeError::InvalidShape {
                text_count: texts.len(),
                type_count: types.len(),
            });
        }
        if self.intrinsic_bootstrap().is_none() {
            return Err(TemplateTypeError::BootstrapUninitialized);
        }
        for type_ in types {
            if self.type_payload(*type_).is_none() {
                return Err(TemplateTypeError::InvalidType(*type_));
            }
        }
        self.get_template_literal_type_worker(texts, types)
    }

    /// Applies a standard-library intrinsic while retaining its symbol identity.
    ///
    /// # Errors
    ///
    /// Returns an error when the symbol is not a supported intrinsic, the target
    /// is invalid, checker bootstrap is absent, or the result cannot be allocated.
    pub fn get_string_mapping_type(
        &mut self,
        symbol: SemanticSymbolId,
        target: TypeId,
    ) -> Result<TypeId, TemplateTypeError> {
        if self.intrinsic_bootstrap().is_none() {
            return Err(TemplateTypeError::BootstrapUninitialized);
        }
        let kind = self.string_mapping_kind(symbol)?;
        if self.type_payload(target).is_none() {
            return Err(TemplateTypeError::InvalidType(target));
        }
        self.get_string_mapping_type_worker(symbol, kind, target)
    }

    /// Tests whether a string-like source satisfies a canonical template pattern.
    ///
    /// # Errors
    ///
    /// Returns an error when either type is foreign, the target is malformed, or
    /// a placeholder contains an invalid or recursive semantic edge.
    pub fn is_type_matched_by_template_literal_type(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, TemplateTypeError> {
        if self.type_payload(source).is_none() {
            return Err(TemplateTypeError::InvalidType(source));
        }
        match self.type_payload(target).map(TypeRecord::data) {
            Some(TypeData::TemplateLiteral(template))
                if !template.types.is_empty()
                    && template.texts.len() == template.types.len() + 1 =>
            {
                self.template_source_matches_pattern(source, target, &mut HashSet::new())
            }
            Some(_) => Err(TemplateTypeError::InvalidTemplate(target)),
            None => Err(TemplateTypeError::InvalidType(target)),
        }
    }

    /// Validates a template-literal index key without allocating semantic records.
    pub(crate) fn is_template_pattern_index_key(&self, key_type: TypeId) -> bool {
        matches!(
            self.type_payload(key_type).map(TypeRecord::data),
            Some(TypeData::TemplateLiteral(template))
                if !template.types.is_empty()
                    && template.texts.len() == template.types.len() + 1
        ) && self
            .is_template_pattern_literal_type(key_type, &mut HashSet::new())
            .unwrap_or(false)
    }

    /// Tests a raw property name against a validated template-literal index key.
    pub(crate) fn template_pattern_index_matches_name(&self, key_type: TypeId, name: &str) -> bool {
        self.is_template_pattern_index_key(key_type)
            && self
                .template_value_matches_pattern(name, key_type, &mut HashSet::new())
                .unwrap_or(false)
    }

    /// Tests whether a string literal belongs to a canonical intrinsic mapping.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign types, malformed mapping symbols, or
    /// recursive template and mapping constraints.
    pub fn is_member_of_string_mapping(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, TemplateTypeError> {
        let source_record = self
            .type_payload(source)
            .ok_or(TemplateTypeError::InvalidType(source))?;
        if self.type_payload(target).is_none() {
            return Err(TemplateTypeError::InvalidType(target));
        }
        let TypeData::Literal(source_literal) = source_record.data() else {
            return Ok(false);
        };
        let LiteralValue::String(value) = &source_literal.value else {
            return Ok(false);
        };
        self.string_mapping_accepts_value(value, target, &mut HashSet::new())
    }

    fn template_source_matches_pattern(
        &self,
        source: TypeId,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let source_record = self
            .type_payload(source)
            .ok_or(TemplateTypeError::InvalidType(source))?;
        match source_record.data() {
            TypeData::Literal(source_literal) => match &source_literal.value {
                LiteralValue::String(value) => {
                    self.template_value_matches_pattern(value, target, active)
                }
                _ => Ok(false),
            },
            TypeData::Union(union) => {
                union
                    .union
                    .types
                    .iter()
                    .try_fold(true, |matches, constituent| {
                        if !matches {
                            return Ok(false);
                        }
                        self.template_source_matches_pattern(*constituent, target, active)
                    })
            }
            TypeData::TemplateLiteral(source_template) => {
                let Some(TypeData::TemplateLiteral(target_template)) =
                    self.type_payload(target).map(TypeRecord::data)
                else {
                    return Err(TemplateTypeError::InvalidTemplate(target));
                };
                if source_template.texts != target_template.texts
                    || source_template.types.len() != target_template.types.len()
                {
                    if target_template.types.len() != 1
                        || !source_template.texts[0].starts_with(&target_template.texts[0])
                        || !source_template
                            .texts
                            .last()
                            .expect("a source template has an ending text")
                            .ends_with(&target_template.texts[1])
                    {
                        return Ok(false);
                    }

                    let placeholder = target_template.types[0];
                    let record = self
                        .type_payload(placeholder)
                        .ok_or(TemplateTypeError::InvalidType(placeholder))?;
                    return Ok(record
                        .flags()
                        .intersects(TypeFlags::ANY | TypeFlags::STRING));
                }
                source_template
                    .types
                    .iter()
                    .zip(&target_template.types)
                    .try_fold(true, |matches, (source, target)| {
                        if !matches {
                            return Ok(false);
                        }
                        self.template_placeholder_type_matches(*source, *target, active)
                    })
            }
            _ => Ok(false),
        }
    }

    fn template_value_matches_pattern(
        &self,
        value: &str,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        if !active.insert(target) {
            return Err(TemplateTypeError::RecursiveType(target));
        }
        let result = self.template_value_matches_pattern_worker(value, target, active);
        active.remove(&target);
        result
    }

    fn template_value_matches_pattern_worker(
        &self,
        value: &str,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let Some(TypeData::TemplateLiteral(template)) =
            self.type_payload(target).map(TypeRecord::data)
        else {
            return Err(TemplateTypeError::InvalidTemplate(target));
        };
        if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
            return Err(TemplateTypeError::InvalidTemplate(target));
        }
        let Some(remainder) = value.strip_prefix(&template.texts[0]) else {
            return Ok(false);
        };
        let Some(remainder) = remainder.strip_suffix(
            template
                .texts
                .last()
                .expect("a validated template has an ending text"),
        ) else {
            return Ok(false);
        };

        let mut position = 0;
        for (index, placeholder) in template.types.iter().enumerate() {
            let capture_end = if index + 1 == template.types.len() {
                remainder.len()
            } else {
                let delimiter = &template.texts[index + 1];
                if delimiter.is_empty() {
                    let Some((first, _)) = split_first_template_code_point(&remainder[position..])
                    else {
                        return Ok(false);
                    };
                    position + first.len()
                } else if let Some(offset) = remainder[position..].find(delimiter) {
                    position + offset
                } else {
                    return Ok(false);
                }
            };
            let capture = &remainder[position..capture_end];
            if !self.template_placeholder_accepts_value(capture, *placeholder, active)? {
                return Ok(false);
            }
            position = capture_end;
            if index + 1 != template.types.len() {
                position += template.texts[index + 1].len();
            }
        }
        Ok(position == remainder.len())
    }

    fn template_placeholder_type_matches(
        &self,
        source: TypeId,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        if source == target {
            return Ok(true);
        }
        let source_record = self
            .type_payload(source)
            .ok_or(TemplateTypeError::InvalidType(source))?;
        let target_record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        if target_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::STRING)
        {
            return Ok(true);
        }
        if let TypeData::Literal(literal) = source_record.data() {
            return match &literal.value {
                LiteralValue::String(value) => {
                    self.template_placeholder_accepts_value(value, target, active)
                }
                LiteralValue::Number(value) => {
                    self.template_placeholder_accepts_value(&value.to_string(), target, active)
                }
                LiteralValue::Boolean(value) => {
                    self.template_placeholder_accepts_value(&value.to_string(), target, active)
                }
                LiteralValue::BigInt(value) => {
                    self.template_placeholder_accepts_value(&value.to_string(), target, active)
                }
                LiteralValue::ComputedEnum => Ok(false),
            };
        }
        if matches!(target_record.data(), TypeData::TemplateLiteral(_)) {
            return self.template_source_matches_pattern(source, target, active);
        }
        Ok(false)
    }

    fn template_placeholder_accepts_value(
        &self,
        value: &str,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        if record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::STRING)
        {
            return Ok(true);
        }
        match record.data() {
            TypeData::Intrinsic(_) if record.flags().intersects(TypeFlags::NUMBER) => {
                let parsed = Number::from_string(value);
                Ok(!value.is_empty() && !parsed.is_nan() && !parsed.is_infinite())
            }
            TypeData::Intrinsic(_) if record.flags().intersects(TypeFlags::BIG_INT) => {
                Ok(valid_bigint_template_fragment(value))
            }
            TypeData::Intrinsic(intrinsic)
                if record
                    .flags()
                    .intersects(TypeFlags::NULL | TypeFlags::UNDEFINED) =>
            {
                Ok(intrinsic.intrinsic_name == value)
            }
            TypeData::Literal(literal) => match &literal.value {
                LiteralValue::String(expected) => Ok(expected == value),
                LiteralValue::Number(expected) => Ok(expected.to_string() == value),
                LiteralValue::Boolean(expected) => Ok(expected.to_string() == value),
                LiteralValue::BigInt(expected) => Ok(expected.to_string() == value),
                LiteralValue::ComputedEnum => Ok(false),
            },
            TypeData::Union(union) => {
                for constituent in &union.union.types {
                    if self.template_placeholder_accepts_value(value, *constituent, active)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            TypeData::TemplateLiteral(_) => {
                self.template_value_matches_pattern(value, target, active)
            }
            TypeData::StringMapping(_) => self.string_mapping_accepts_value(value, target, active),
            TypeData::TypeParameter(parameter) => match parameter.constraint {
                Some(constraint) if constraint != target => {
                    self.template_placeholder_accepts_value(value, constraint, active)
                }
                _ => Ok(false),
            },
            TypeData::Intersection(intersection) => intersection
                .intersection
                .types
                .iter()
                .try_fold(true, |matches, constituent| {
                    if !matches {
                        return Ok(false);
                    }
                    if self
                        .intrinsic_bootstrap()
                        .is_some_and(|bootstrap| bootstrap.empty_type_literal_type == *constituent)
                    {
                        return Ok(true);
                    }
                    self.template_placeholder_accepts_value(value, *constituent, active)
                }),
            _ => Ok(false),
        }
    }

    fn string_mapping_accepts_value(
        &self,
        value: &str,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        if !matches!(record.data(), TypeData::StringMapping(_)) {
            return self.template_placeholder_accepts_value(value, target, active);
        }
        let (mapped, inner) = self.apply_string_mapping_chain(value, target, active)?;
        if mapped != value {
            return Ok(false);
        }
        self.string_mapping_accepts_value(value, inner, active)
    }

    fn apply_string_mapping_chain(
        &self,
        value: &str,
        target: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<(String, TypeId), TemplateTypeError> {
        let record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        let TypeData::StringMapping(mapping) = record.data() else {
            return Ok((value.to_owned(), target));
        };
        if !active.insert(target) {
            return Err(TemplateTypeError::RecursiveType(target));
        }
        let result = (|| {
            let (mapped, inner) = self.apply_string_mapping_chain(value, mapping.target, active)?;
            let symbol = record
                .symbol()
                .ok_or(TemplateTypeError::InvalidTemplate(target))?;
            let kind = self.string_mapping_kind(symbol)?;
            Ok((kind.apply(&mapped), inner))
        })();
        active.remove(&target);
        result
    }

    pub(super) fn string_mapping_kind(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<StringMappingKind, TemplateTypeError> {
        self.symbol(symbol)
            .ok_or(TemplateTypeError::InvalidMappingSymbol(symbol))?
            .name()
            .as_utf8()
            .and_then(StringMappingKind::from_name)
            .ok_or(TemplateTypeError::UnsupportedMappingSymbol(symbol))
    }

    /// Computes the upstream union cross-product estimate without allocating.
    ///
    /// # Errors
    ///
    /// Returns an error when an input does not belong to this store or a union
    /// contains fewer than two constituents.
    pub fn get_template_cross_product_union_size(
        &self,
        types: &[TypeId],
    ) -> Result<usize, TemplateTypeError> {
        let mut size = 1usize;
        for type_ in types {
            let record = self
                .type_payload(*type_)
                .ok_or(TemplateTypeError::InvalidType(*type_))?;
            if record.flags().intersects(TypeFlags::NEVER) {
                return Ok(0);
            }
            if record.flags().intersects(TypeFlags::UNION) {
                let TypeData::Union(union) = record.data() else {
                    return Err(TemplateTypeError::InvalidUnion(*type_));
                };
                if union.union.types.len() < 2 {
                    return Err(TemplateTypeError::InvalidUnion(*type_));
                }
                size = size.saturating_mul(union.union.types.len());
            }
        }
        Ok(size)
    }

    pub(super) fn cached_resolved_template_literal_type(
        &self,
        texts: &[String],
        types: &[TypeId],
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        if texts.len() != types.len().saturating_add(1) {
            return Err(TemplateTypeError::InvalidShape {
                text_count: texts.len(),
                type_count: types.len(),
            });
        }
        if self.intrinsic_bootstrap().is_none() {
            return Err(TemplateTypeError::BootstrapUninitialized);
        }
        for type_ in types {
            if self.type_payload(*type_).is_none() {
                return Err(TemplateTypeError::InvalidType(*type_));
            }
        }
        self.cached_resolved_template_literal_type_worker(texts, types)
    }

    fn cached_resolved_template_literal_type_worker(
        &self,
        texts: &[String],
        types: &[TypeId],
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        if let Some(index) = types.iter().position(|type_| {
            self.type_payload(*type_).is_some_and(|record| {
                record
                    .flags()
                    .intersects(TypeFlags::NEVER | TypeFlags::UNION)
            })
        }) {
            return self.cached_distributed_template_literal_type(texts, types, index);
        }

        let bootstrap = self
            .intrinsic_bootstrap()
            .ok_or(TemplateTypeError::BootstrapUninitialized)?;
        if types.contains(&bootstrap.wildcard_type) {
            return Ok(Some(bootstrap.wildcard_type));
        }

        let mut normalized = NormalizedTemplate {
            current: texts[0].clone(),
            ..NormalizedTemplate::default()
        };
        if !self.append_template_spans(texts, types, &mut normalized, &mut HashSet::new())? {
            return Ok(Some(bootstrap.string_type));
        }
        if normalized.types.is_empty() {
            return Ok(bootstrap.cached_string_literal_type(&normalized.current));
        }
        normalized.texts.push(normalized.current);

        if normalized.texts.iter().all(String::is_empty) {
            if normalized.types.iter().all(|type_| {
                self.type_payload(*type_)
                    .is_some_and(|record| record.flags().intersects(TypeFlags::STRING))
            }) {
                return Ok(Some(bootstrap.string_type));
            }
            if let [placeholder] = normalized.types.as_slice()
                && self.is_template_pattern_literal_type(*placeholder, &mut HashSet::new())?
            {
                return Ok(Some(*placeholder));
            }
        }
        self.find_template_literal_type(&normalized.texts, &normalized.types)
    }

    fn cached_distributed_template_literal_type(
        &self,
        texts: &[String],
        types: &[TypeId],
        index: usize,
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        let size = self.get_template_cross_product_union_size(types)?;
        if size >= MAX_TEMPLATE_UNION_SIZE {
            return Err(TemplateTypeError::CrossProductTooLarge {
                size,
                limit: MAX_TEMPLATE_UNION_SIZE,
            });
        }

        let record = self
            .type_payload(types[index])
            .ok_or(TemplateTypeError::InvalidType(types[index]))?;
        if record.flags().intersects(TypeFlags::NEVER) {
            return Ok(Some(types[index]));
        }
        let TypeData::Union(union) = record.data() else {
            return Err(TemplateTypeError::InvalidUnion(types[index]));
        };
        let mut selected = types.to_vec();
        let mut mapped = Vec::with_capacity(union.union.types.len());
        for constituent in &union.union.types {
            selected[index] = *constituent;
            let Some(result) =
                self.cached_resolved_template_literal_type_worker(texts, &selected)?
            else {
                return Ok(None);
            };
            mapped.push(result);
        }
        self.cached_template_result_union(&mapped)
    }

    fn get_template_literal_type_worker(
        &mut self,
        texts: &[String],
        types: &[TypeId],
    ) -> Result<TypeId, TemplateTypeError> {
        if let Some(index) = types.iter().position(|type_| {
            self.type_payload(*type_).is_some_and(|record| {
                record
                    .flags()
                    .intersects(TypeFlags::NEVER | TypeFlags::UNION)
            })
        }) {
            let size = self.get_template_cross_product_union_size(types)?;
            if size >= MAX_TEMPLATE_UNION_SIZE {
                return Err(TemplateTypeError::CrossProductTooLarge {
                    size,
                    limit: MAX_TEMPLATE_UNION_SIZE,
                });
            }

            let record = self
                .type_payload(types[index])
                .ok_or(TemplateTypeError::InvalidType(types[index]))?;
            if record.flags().intersects(TypeFlags::NEVER) {
                return Ok(types[index]);
            }
            let TypeData::Union(union) = record.data() else {
                return Err(TemplateTypeError::InvalidUnion(types[index]));
            };
            let constituents = union.union.types.clone();
            let mut mapped = Vec::with_capacity(constituents.len());
            let mut selected = types.to_vec();
            for constituent in constituents {
                if self.type_payload(constituent).is_none() {
                    return Err(TemplateTypeError::InvalidType(constituent));
                }
                selected[index] = constituent;
                mapped.push(self.get_template_literal_type_worker(texts, &selected)?);
            }
            return self.template_result_union(&mapped);
        }

        let (wildcard, string) = {
            let bootstrap = self
                .intrinsic_bootstrap()
                .ok_or(TemplateTypeError::BootstrapUninitialized)?;
            (bootstrap.wildcard_type, bootstrap.string_type)
        };
        if types.contains(&wildcard) {
            return Ok(wildcard);
        }

        let mut normalized = NormalizedTemplate {
            current: texts[0].clone(),
            ..NormalizedTemplate::default()
        };
        if !self.append_template_spans(texts, types, &mut normalized, &mut HashSet::new())? {
            return Ok(string);
        }
        if normalized.types.is_empty() {
            return self
                .regular_string_literal_type(normalized.current)
                .map_err(Into::into);
        }
        normalized.texts.push(normalized.current);

        if normalized.texts.iter().all(String::is_empty) {
            if normalized.types.iter().all(|type_| {
                self.type_payload(*type_)
                    .is_some_and(|record| record.flags().intersects(TypeFlags::STRING))
            }) {
                return Ok(string);
            }
            if let [placeholder] = normalized.types.as_slice()
                && self.is_template_pattern_literal_type(*placeholder, &mut HashSet::new())?
            {
                return Ok(*placeholder);
            }
        }

        if let Some(existing) =
            self.find_template_literal_type(&normalized.texts, &normalized.types)?
        {
            return Ok(existing);
        }
        if !self.try_reserve_types(1) {
            return Err(TemplateTypeError::Capacity);
        }
        self.alloc_template_literal_type(normalized.texts, normalized.types)
            .ok_or(TemplateTypeError::Capacity)
    }

    fn append_template_spans(
        &self,
        texts: &[String],
        types: &[TypeId],
        normalized: &mut NormalizedTemplate,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        for (index, type_) in types.iter().copied().enumerate() {
            let record = self
                .type_payload(type_)
                .ok_or(TemplateTypeError::InvalidType(type_))?;
            if record
                .flags()
                .intersects(TypeFlags::LITERAL | TypeFlags::NULL | TypeFlags::UNDEFINED)
            {
                append_js_string(
                    &mut normalized.current,
                    &Self::template_string_for_type(type_, record)?,
                );
                append_js_string(&mut normalized.current, &texts[index + 1]);
            } else if record.flags().intersects(TypeFlags::TEMPLATE_LITERAL) {
                let TypeData::TemplateLiteral(template) = record.data() else {
                    return Err(TemplateTypeError::InvalidTemplate(type_));
                };
                if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
                    return Err(TemplateTypeError::InvalidTemplate(type_));
                }
                if !visiting.insert(type_) {
                    return Err(TemplateTypeError::RecursiveType(type_));
                }
                append_js_string(&mut normalized.current, &template.texts[0]);
                let added = self.append_template_spans(
                    &template.texts,
                    &template.types,
                    normalized,
                    visiting,
                )?;
                visiting.remove(&type_);
                if !added {
                    return Ok(false);
                }
                append_js_string(&mut normalized.current, &texts[index + 1]);
            } else if self.is_template_generic_index_type(type_, &mut HashSet::new())?
                || self.is_template_pattern_placeholder(type_, &mut HashSet::new())?
            {
                normalized.types.push(type_);
                normalized
                    .texts
                    .push(std::mem::take(&mut normalized.current));
                append_js_string(&mut normalized.current, &texts[index + 1]);
            } else {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn template_string_for_type(
        type_: TypeId,
        record: &TypeRecord,
    ) -> Result<String, TemplateTypeError> {
        match record.data() {
            TypeData::Literal(literal) => match &literal.value {
                LiteralValue::String(value) => Ok(value.clone()),
                LiteralValue::Number(value) => Ok(value.to_string()),
                LiteralValue::Boolean(value) => Ok(value.to_string()),
                LiteralValue::BigInt(value) => Ok(value.to_string()),
                LiteralValue::ComputedEnum => Err(TemplateTypeError::InvalidLiteral(type_)),
            },
            TypeData::Intrinsic(intrinsic)
                if record
                    .flags()
                    .intersects(TypeFlags::NULL | TypeFlags::UNDEFINED) =>
            {
                Ok(intrinsic.intrinsic_name.clone())
            }
            _ => Err(TemplateTypeError::InvalidLiteral(type_)),
        }
    }

    fn find_template_literal_type(
        &self,
        texts: &[String],
        types: &[TypeId],
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        let bootstrap = self
            .intrinsic_bootstrap()
            .ok_or(TemplateTypeError::BootstrapUninitialized)?;
        if let Some(existing) = bootstrap.cached_template_literal_type(texts, types) {
            let Some(TypeData::TemplateLiteral(template)) =
                self.type_payload(existing).map(TypeRecord::data)
            else {
                return Err(TemplateTypeError::InvalidTemplate(existing));
            };
            if template.texts != texts || template.types != types {
                return Err(TemplateTypeError::InvalidTemplate(existing));
            }
            return Ok(Some(existing));
        }

        Ok(self.types().find_map(|(id, record)| match record.data() {
            TypeData::TemplateLiteral(template)
                if template.texts == texts && template.types == types =>
            {
                Some(id)
            }
            _ => None,
        }))
    }

    fn is_template_generic_index_type(
        &self,
        type_: TypeId,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(TemplateTypeError::InvalidType(type_))?;
        if record
            .flags()
            .intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE | TypeFlags::INDEX)
        {
            return Ok(true);
        }
        if record
            .flags()
            .intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
        {
            return self
                .is_template_pattern_literal_type(type_, visiting)
                .map(|pattern| !pattern);
        }
        if let TypeData::Intersection(intersection) = record.data() {
            if !visiting.insert(type_) {
                return Err(TemplateTypeError::RecursiveType(type_));
            }
            for constituent in &intersection.intersection.types {
                if self.is_template_generic_index_type(*constituent, visiting)? {
                    visiting.remove(&type_);
                    return Ok(true);
                }
            }
            visiting.remove(&type_);
        }
        Ok(false)
    }

    fn is_template_pattern_placeholder(
        &self,
        type_: TypeId,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(TemplateTypeError::InvalidType(type_))?;
        if let TypeData::Intersection(intersection) = record.data() {
            if !visiting.insert(type_) {
                return Err(TemplateTypeError::RecursiveType(type_));
            }
            let mut saw_placeholder = false;
            for constituent in &intersection.intersection.types {
                let constituent_record = self
                    .type_payload(*constituent)
                    .ok_or(TemplateTypeError::InvalidType(*constituent))?;
                if constituent_record
                    .flags()
                    .intersects(TypeFlags::LITERAL | TypeFlags::NULLABLE)
                    || self.is_template_pattern_placeholder(*constituent, visiting)?
                {
                    saw_placeholder = true;
                } else if !constituent_record.flags().intersects(TypeFlags::OBJECT) {
                    visiting.remove(&type_);
                    return Ok(false);
                }
            }
            visiting.remove(&type_);
            return Ok(saw_placeholder);
        }
        if record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::STRING | TypeFlags::NUMBER | TypeFlags::BIG_INT)
        {
            return Ok(true);
        }
        self.is_template_pattern_literal_type(type_, visiting)
    }

    fn is_template_pattern_literal_type(
        &self,
        type_: TypeId,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, TemplateTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(TemplateTypeError::InvalidType(type_))?;
        match record.data() {
            TypeData::TemplateLiteral(template) => {
                if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
                    return Err(TemplateTypeError::InvalidTemplate(type_));
                }
                if !visiting.insert(type_) {
                    return Err(TemplateTypeError::RecursiveType(type_));
                }
                for placeholder in &template.types {
                    if !self.is_template_pattern_placeholder(*placeholder, visiting)? {
                        visiting.remove(&type_);
                        return Ok(false);
                    }
                }
                visiting.remove(&type_);
                Ok(true)
            }
            TypeData::StringMapping(mapping) => {
                if !visiting.insert(type_) {
                    return Err(TemplateTypeError::RecursiveType(type_));
                }
                let result = self.is_template_pattern_placeholder(mapping.target, visiting);
                visiting.remove(&type_);
                result
            }
            _ => Ok(false),
        }
    }

    pub(super) fn cached_resolved_string_mapping_type(
        &self,
        symbol: SemanticSymbolId,
        target: TypeId,
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        if self.intrinsic_bootstrap().is_none() {
            return Err(TemplateTypeError::BootstrapUninitialized);
        }
        let kind = self.string_mapping_kind(symbol)?;
        if self.type_payload(target).is_none() {
            return Err(TemplateTypeError::InvalidType(target));
        }
        self.cached_resolved_string_mapping_type_worker(symbol, kind, target)
    }

    fn cached_resolved_string_mapping_type_worker(
        &self,
        symbol: SemanticSymbolId,
        kind: StringMappingKind,
        target: TypeId,
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        let record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        if record.flags().intersects(TypeFlags::NEVER) {
            return Ok(Some(target));
        }
        match record.data() {
            TypeData::Union(union) => {
                if union.union.types.len() < 2 {
                    return Err(TemplateTypeError::InvalidUnion(target));
                }
                let mut mapped = Vec::with_capacity(union.union.types.len());
                for constituent in &union.union.types {
                    let Some(result) = self.cached_resolved_string_mapping_type_worker(
                        symbol,
                        kind,
                        *constituent,
                    )?
                    else {
                        return Ok(None);
                    };
                    mapped.push(result);
                }
                if mapped == union.union.types {
                    Ok(Some(target))
                } else {
                    self.cached_template_result_union(&mapped)
                }
            }
            TypeData::Literal(literal) if record.flags().intersects(TypeFlags::STRING_LITERAL) => {
                let LiteralValue::String(value) = &literal.value else {
                    return Err(TemplateTypeError::InvalidLiteral(target));
                };
                Ok(self
                    .intrinsic_bootstrap()
                    .and_then(|bootstrap| bootstrap.cached_string_literal_type(&kind.apply(value))))
            }
            TypeData::TemplateLiteral(template) => {
                self.cached_mapped_template_literal_type(symbol, kind, target, template)
            }
            TypeData::StringMapping(_) if record.symbol() == Some(symbol) => Ok(Some(target)),
            _ if record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::STRING | TypeFlags::STRING_MAPPING)
                || self.is_template_generic_index_type(target, &mut HashSet::new())? =>
            {
                Ok(self.cached_generic_string_mapping_type(symbol, target))
            }
            _ if self.is_template_pattern_placeholder(target, &mut HashSet::new())? => {
                let Some(template) = self.cached_resolved_template_literal_type_worker(
                    &[String::new(), String::new()],
                    &[target],
                )?
                else {
                    return Ok(None);
                };
                Ok(self.cached_generic_string_mapping_type(symbol, template))
            }
            _ => Ok(Some(target)),
        }
    }

    fn cached_mapped_template_literal_type(
        &self,
        symbol: SemanticSymbolId,
        kind: StringMappingKind,
        target: TypeId,
        template: &super::type_records::TemplateLiteralTypeData,
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        let mut texts = template.texts.clone();
        let mut types = template.types.clone();
        if types.is_empty() || texts.len() != types.len() + 1 {
            return Err(TemplateTypeError::InvalidTemplate(target));
        }
        match kind {
            StringMappingKind::Uppercase | StringMappingKind::Lowercase => {
                for text in &mut texts {
                    *text = kind.apply(text);
                }
                for type_ in &mut types {
                    let Some(mapped) =
                        self.cached_resolved_string_mapping_type_worker(symbol, kind, *type_)?
                    else {
                        return Ok(None);
                    };
                    *type_ = mapped;
                }
            }
            StringMappingKind::Capitalize | StringMappingKind::Uncapitalize => {
                if texts[0].is_empty() {
                    let Some(mapped) =
                        self.cached_resolved_string_mapping_type_worker(symbol, kind, types[0])?
                    else {
                        return Ok(None);
                    };
                    types[0] = mapped;
                } else {
                    texts[0] = kind.apply(&texts[0]);
                }
            }
        }
        self.cached_resolved_template_literal_type_worker(&texts, &types)
    }

    fn cached_generic_string_mapping_type(
        &self,
        symbol: SemanticSymbolId,
        target: TypeId,
    ) -> Option<TypeId> {
        self.types().find_map(|(id, record)| match record.data() {
            TypeData::StringMapping(mapping)
                if record.symbol() == Some(symbol) && mapping.target == target =>
            {
                Some(id)
            }
            _ => None,
        })
    }

    fn get_string_mapping_type_worker(
        &mut self,
        symbol: SemanticSymbolId,
        kind: StringMappingKind,
        target: TypeId,
    ) -> Result<TypeId, TemplateTypeError> {
        let record = self
            .type_payload(target)
            .ok_or(TemplateTypeError::InvalidType(target))?;
        if record.flags().intersects(TypeFlags::NEVER) {
            return Ok(target);
        }
        match record.data() {
            TypeData::Union(union) => {
                let constituents = union.union.types.clone();
                if constituents.len() < 2 {
                    return Err(TemplateTypeError::InvalidUnion(target));
                }
                let mut mapped = Vec::with_capacity(constituents.len());
                for constituent in &constituents {
                    mapped.push(self.get_string_mapping_type_worker(symbol, kind, *constituent)?);
                }
                if mapped == constituents {
                    Ok(target)
                } else {
                    self.template_result_union(&mapped)
                }
            }
            TypeData::Literal(literal) if record.flags().intersects(TypeFlags::STRING_LITERAL) => {
                let LiteralValue::String(value) = &literal.value else {
                    return Err(TemplateTypeError::InvalidLiteral(target));
                };
                self.regular_string_literal_type(kind.apply(value))
                    .map_err(Into::into)
            }
            TypeData::TemplateLiteral(template) => {
                let mut texts = template.texts.clone();
                let mut types = template.types.clone();
                if types.is_empty() || texts.len() != types.len() + 1 {
                    return Err(TemplateTypeError::InvalidTemplate(target));
                }
                match kind {
                    StringMappingKind::Uppercase | StringMappingKind::Lowercase => {
                        for text in &mut texts {
                            *text = kind.apply(text);
                        }
                        for type_ in &mut types {
                            *type_ = self.get_string_mapping_type_worker(symbol, kind, *type_)?;
                        }
                    }
                    StringMappingKind::Capitalize | StringMappingKind::Uncapitalize => {
                        if texts[0].is_empty() {
                            types[0] =
                                self.get_string_mapping_type_worker(symbol, kind, types[0])?;
                        } else {
                            texts[0] = kind.apply(&texts[0]);
                        }
                    }
                }
                self.get_template_literal_type_worker(&texts, &types)
            }
            TypeData::StringMapping(_) if record.symbol() == Some(symbol) => Ok(target),
            _ if record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::STRING | TypeFlags::STRING_MAPPING)
                || self.is_template_generic_index_type(target, &mut HashSet::new())? =>
            {
                self.get_string_mapping_type_for_generic_type(symbol, target)
            }
            _ if self.is_template_pattern_placeholder(target, &mut HashSet::new())? => {
                let template = self
                    .get_template_literal_type_worker(&[String::new(), String::new()], &[target])?;
                self.get_string_mapping_type_for_generic_type(symbol, template)
            }
            _ => Ok(target),
        }
    }

    fn get_string_mapping_type_for_generic_type(
        &mut self,
        symbol: SemanticSymbolId,
        target: TypeId,
    ) -> Result<TypeId, TemplateTypeError> {
        if let Some(existing) = self.cached_generic_string_mapping_type(symbol, target) {
            return Ok(existing);
        }
        if !self.try_reserve_types(1) {
            return Err(TemplateTypeError::Capacity);
        }
        self.alloc_string_mapping_type(Some(symbol), target)
            .ok_or(TemplateTypeError::Capacity)
    }

    pub(super) fn template_result_union(
        &mut self,
        types: &[TypeId],
    ) -> Result<TypeId, TemplateTypeError> {
        let flattened = match self.plan_template_result_union(types)? {
            TemplateUnionPlan::Existing(existing) => return Ok(existing),
            TemplateUnionPlan::Constituents(types) => types,
        };

        if flattened
            .iter()
            .all(|type_| self.validate_union_constituent(*type_).is_ok())
        {
            let mut prepared = self.prepare_type_query_types(&[], &[], &[], 1, 0)?;
            return self
                .literal_union_type_prepared(&flattened, None, &mut prepared)
                .map_err(Into::into);
        }

        if let Some(existing) = self.find_template_result_union(&flattened) {
            return Ok(existing);
        }

        if !self.try_reserve_types(1) {
            return Err(TemplateTypeError::Capacity);
        }
        self.alloc_union_type(ObjectFlags::NONE, flattened)
            .ok_or(TemplateTypeError::Capacity)
    }

    pub(super) fn cached_template_result_union(
        &self,
        types: &[TypeId],
    ) -> Result<Option<TypeId>, TemplateTypeError> {
        match self.plan_template_result_union(types)? {
            TemplateUnionPlan::Existing(existing) => Ok(Some(existing)),
            TemplateUnionPlan::Constituents(types) => Ok(self.find_template_result_union(&types)),
        }
    }

    fn plan_template_result_union(
        &self,
        types: &[TypeId],
    ) -> Result<TemplateUnionPlan, TemplateTypeError> {
        let bootstrap = self
            .intrinsic_bootstrap()
            .ok_or(TemplateTypeError::BootstrapUninitialized)?;
        let mut flattened = Vec::with_capacity(types.len());
        self.flatten_template_union_types(types, &mut flattened, &mut HashSet::new())?;
        flattened.retain(|type_| {
            self.type_payload(*type_)
                .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
        });
        flattened.sort_by(|left, right| self.compare_template_union_types(*left, *right));
        flattened.dedup();

        if flattened.iter().any(|type_| {
            self.type_payload(*type_)
                .is_some_and(|record| record.flags().intersects(TypeFlags::ANY))
        }) {
            let existing = if flattened.contains(&bootstrap.wildcard_type) {
                bootstrap.wildcard_type
            } else if flattened.contains(&bootstrap.error_type) {
                bootstrap.error_type
            } else {
                bootstrap.any_type
            };
            return Ok(TemplateUnionPlan::Existing(existing));
        }
        if flattened.iter().any(|type_| {
            self.type_payload(*type_)
                .is_some_and(|record| record.flags().intersects(TypeFlags::UNKNOWN))
        }) {
            return Ok(TemplateUnionPlan::Existing(bootstrap.unknown_type));
        }

        let has_string = flattened.contains(&bootstrap.string_type);
        let has_number = flattened.contains(&bootstrap.number_type);
        let has_bigint = flattened.contains(&bootstrap.bigint_type);
        if has_string || has_number || has_bigint {
            flattened.retain(|type_| {
                let Some(record) = self.type_payload(*type_) else {
                    return false;
                };
                !(has_string
                    && record.flags().intersects(
                        TypeFlags::STRING_LITERAL
                            | TypeFlags::TEMPLATE_LITERAL
                            | TypeFlags::STRING_MAPPING,
                    )
                    || has_number && record.flags().intersects(TypeFlags::NUMBER_LITERAL)
                    || has_bigint && record.flags().intersects(TypeFlags::BIG_INT_LITERAL))
            });
        }

        self.remove_literals_matched_by_template_patterns(&mut flattened)?;

        match flattened.as_slice() {
            [] => Ok(TemplateUnionPlan::Existing(bootstrap.never_type)),
            [single] => Ok(TemplateUnionPlan::Existing(*single)),
            _ => Ok(TemplateUnionPlan::Constituents(flattened)),
        }
    }

    fn remove_literals_matched_by_template_patterns(
        &self,
        types: &mut Vec<TypeId>,
    ) -> Result<(), TemplateTypeError> {
        let mut patterns = Vec::new();
        for type_ in types.iter().copied() {
            let record = self
                .type_payload(type_)
                .ok_or(TemplateTypeError::InvalidType(type_))?;
            if record
                .flags()
                .intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
                && self.is_template_pattern_literal_type(type_, &mut HashSet::new())?
            {
                patterns.push(type_);
            }
        }
        if patterns.is_empty() {
            return Ok(());
        }

        let mut index = types.len();
        while index != 0 {
            index -= 1;
            let candidate = types[index];
            let record = self
                .type_payload(candidate)
                .ok_or(TemplateTypeError::InvalidType(candidate))?;
            if !record.flags().intersects(TypeFlags::STRING_LITERAL) {
                continue;
            }
            for pattern in &patterns {
                let matched = match self.type_payload(*pattern).map(TypeRecord::data) {
                    Some(TypeData::TemplateLiteral(_)) => {
                        self.is_type_matched_by_template_literal_type(candidate, *pattern)?
                    }
                    Some(TypeData::StringMapping(_)) => {
                        self.is_member_of_string_mapping(candidate, *pattern)?
                    }
                    _ => return Err(TemplateTypeError::InvalidType(*pattern)),
                };
                if matched {
                    types.remove(index);
                    break;
                }
            }
        }
        Ok(())
    }

    fn find_template_result_union(&self, types: &[TypeId]) -> Option<TypeId> {
        self.intrinsic_bootstrap()
            .and_then(|bootstrap| bootstrap.cached_union_type(types))
            .or_else(|| {
                self.types().find_map(|(id, record)| match record.data() {
                    TypeData::Union(union)
                        if record.alias().is_none()
                            && union.origin.is_none()
                            && union.union.types == types =>
                    {
                        Some(id)
                    }
                    _ => None,
                })
            })
    }

    fn flatten_template_union_types(
        &self,
        types: &[TypeId],
        flattened: &mut Vec<TypeId>,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<(), TemplateTypeError> {
        for type_ in types {
            let record = self
                .type_payload(*type_)
                .ok_or(TemplateTypeError::InvalidType(*type_))?;
            if let TypeData::Union(union) = record.data() {
                if !visiting.insert(*type_) {
                    return Err(TemplateTypeError::RecursiveType(*type_));
                }
                self.flatten_template_union_types(&union.union.types, flattened, visiting)?;
                visiting.remove(type_);
            } else {
                flattened.push(*type_);
            }
        }
        Ok(())
    }

    fn compare_template_union_types(&self, left: TypeId, right: TypeId) -> Ordering {
        if left == right {
            return Ordering::Equal;
        }
        let left_record = self
            .type_payload(left)
            .expect("template union constituents were validated");
        let right_record = self
            .type_payload(right)
            .expect("template union constituents were validated");
        let flags = left_record.flags().cmp(&right_record.flags());
        if flags != Ordering::Equal {
            return flags;
        }
        if let (TypeData::Literal(left), TypeData::Literal(right)) =
            (left_record.data(), right_record.data())
        {
            let values = match (&left.value, &right.value) {
                (LiteralValue::String(left), LiteralValue::String(right)) => left.cmp(right),
                (LiteralValue::Number(left), LiteralValue::Number(right)) => {
                    left.partial_cmp(right).unwrap_or(Ordering::Equal)
                }
                (LiteralValue::Boolean(left), LiteralValue::Boolean(right)) => left.cmp(right),
                _ => Ordering::Equal,
            };
            if values != Ordering::Equal {
                return values;
            }
        }
        left.get().cmp(&right.get())
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{decode_js_string, encode_js_string};
    use ts_binder::{CheckFlags, EscapedName, SymbolFlags};
    use ts_core::JsString;

    use super::{
        CanonicalTypeMapperStore, MAX_TEMPLATE_UNION_SIZE, StringMappingKind, TemplateTypeError,
        split_first_template_code_point,
    };
    use crate::semantic::{
        IntrinsicBootstrapOptions,
        type_records::{LiteralValue, TypeData, TypeRecord},
        types::ObjectFlags,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn string_literal(store: &mut CanonicalTypeMapperStore, value: &str) -> super::TypeId {
        store
            .get_template_literal_type(&[value.to_owned()], &[])
            .unwrap()
    }

    #[test]
    fn template_code_point_splitting_preserves_supplementary_and_lone_surrogates() {
        assert_eq!(split_first_template_code_point("abc"), Some(("a", "bc")));
        assert_eq!(
            split_first_template_code_point("\u{3042}\u{3044}"),
            Some(("\u{3042}", "\u{3044}"))
        );
        assert_eq!(
            split_first_template_code_point("\u{1f600}tail"),
            Some(("\u{1f600}", "tail"))
        );

        let encoded = encode_js_string(&JsString::from_units(vec![0xd800, u16::from(b'x')]));
        let (first, rest) = split_first_template_code_point(&encoded).unwrap();
        assert_eq!(decode_js_string(first).as_units(), &[0xd800]);
        assert_eq!(rest, "x");

        let real_marker = encode_js_string(&JsString::from_utf8("\u{10fffd}x"));
        let (first, rest) = split_first_template_code_point(&real_marker).unwrap();
        assert_eq!(decode_js_string(first), JsString::from_utf8("\u{10fffd}"));
        assert_eq!(rest, "x");
        assert_eq!(split_first_template_code_point(""), None);
    }

    #[test]
    fn template_pattern_index_signatures_accept_only_matching_string_keys() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let pattern = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();
        let matching = string_literal(&mut store, "do-save");
        let empty_suffix = string_literal(&mut store, "do-");
        let namespaced = string_literal(&mut store, "ns:thing");
        let bare = string_literal(&mut store, "do");

        assert_eq!(
            store.is_type_matched_by_template_literal_type(matching, pattern),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(empty_suffix, pattern),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(namespaced, pattern),
            Ok(false)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(bare, pattern),
            Ok(false)
        );

        assert!(store.is_template_pattern_index_key(pattern));
        assert!(!store.is_template_pattern_index_key(string));
        assert!(store.template_pattern_index_matches_name(pattern, "do-save"));
        assert!(store.template_pattern_index_matches_name(pattern, "do-"));
        assert!(!store.template_pattern_index_matches_name(pattern, "ns:thing"));
        assert!(!store.template_pattern_index_matches_name(string, "do-save"));
    }

    #[test]
    fn template_patterns_accept_narrower_sources_with_different_static_boundaries() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let target = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();
        let numeric_target = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[number])
            .unwrap();
        let narrowed = store
            .get_template_literal_type(&["do-prefix-".to_owned(), String::new()], &[number])
            .unwrap();
        let wrong_prefix = store
            .get_template_literal_type(&["undo-".to_owned(), String::new()], &[number])
            .unwrap();
        let suffixed_target = store
            .get_template_literal_type(&["do-".to_owned(), "-done".to_owned()], &[string])
            .unwrap();
        let matching_suffix = store
            .get_template_literal_type(
                &["do-prefix-".to_owned(), "-extra-done".to_owned()],
                &[number],
            )
            .unwrap();
        let wrong_suffix = store
            .get_template_literal_type(&["do-prefix-".to_owned(), "-pending".to_owned()], &[number])
            .unwrap();

        assert_eq!(
            store.is_type_matched_by_template_literal_type(narrowed, target),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(wrong_prefix, target),
            Ok(false)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(narrowed, numeric_target),
            Ok(false)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(matching_suffix, suffixed_target),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(wrong_suffix, suffixed_target),
            Ok(false)
        );
    }

    #[test]
    fn template_pattern_placeholders_validate_number_bigint_and_intrinsic_casing() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let bigint = bootstrap.bigint_type;
        let numeric = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[number])
            .unwrap();
        let integral = store
            .get_template_literal_type(&["big-".to_owned(), String::new()], &[bigint])
            .unwrap();
        let uppercase_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let uppercase = store
            .get_string_mapping_type(uppercase_symbol, string)
            .unwrap();
        let upper_pattern = store
            .get_template_literal_type(&["key-".to_owned(), String::new()], &[uppercase])
            .unwrap();

        for (pattern, value, expected) in [
            (numeric, "id-12.5", true),
            (numeric, "id-NaN", false),
            (numeric, "id-Infinity", false),
            (numeric, "id-", false),
            (integral, "big--42", true),
            (integral, "big-0xff", true),
            (integral, "big-1.5", false),
            (upper_pattern, "key-ABC", true),
            (upper_pattern, "key-Abc", false),
        ] {
            let source = string_literal(&mut store, value);
            assert_eq!(
                store.is_type_matched_by_template_literal_type(source, pattern),
                Ok(expected),
                "pattern value {value}"
            );
        }

        let upper_value = string_literal(&mut store, "ABC");
        let lower_value = string_literal(&mut store, "abc");
        assert_eq!(
            store.is_member_of_string_mapping(upper_value, uppercase),
            Ok(true)
        );
        assert_eq!(
            store.is_member_of_string_mapping(lower_value, uppercase),
            Ok(false)
        );
    }

    #[test]
    fn nested_intrinsic_mappings_apply_inner_operations_before_outer_operations() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let uppercase_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let lowercase_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Lowercase"),
            CheckFlags::NONE,
        );
        let lowercase = store
            .get_string_mapping_type(lowercase_symbol, string)
            .unwrap();
        let uppercase_after_lowercase = store
            .get_string_mapping_type(uppercase_symbol, lowercase)
            .unwrap();
        let uppercase = store
            .get_string_mapping_type(uppercase_symbol, string)
            .unwrap();
        let lowercase_after_uppercase = store
            .get_string_mapping_type(lowercase_symbol, uppercase)
            .unwrap();
        let upper_value = string_literal(&mut store, "FOO");
        let lower_value = string_literal(&mut store, "foo");
        let mixed_value = string_literal(&mut store, "Foo");
        let encoded_upper = encode_js_string(&JsString::from_units(vec![
            0xd800,
            u16::from(b'F'),
            u16::from(b'O'),
            u16::from(b'O'),
        ]));
        let encoded_lower = encode_js_string(&JsString::from_units(vec![
            0xd800,
            u16::from(b'f'),
            u16::from(b'o'),
            u16::from(b'o'),
        ]));
        let lone_upper = string_literal(&mut store, &encoded_upper);
        let lone_lower = string_literal(&mut store, &encoded_lower);

        assert_eq!(
            store.is_member_of_string_mapping(upper_value, uppercase_after_lowercase),
            Ok(true)
        );
        assert_eq!(
            store.is_member_of_string_mapping(lower_value, uppercase_after_lowercase),
            Ok(false)
        );
        assert_eq!(
            store.is_member_of_string_mapping(mixed_value, uppercase_after_lowercase),
            Ok(false)
        );
        assert_eq!(
            store.is_member_of_string_mapping(lower_value, lowercase_after_uppercase),
            Ok(true)
        );
        assert_eq!(
            store.is_member_of_string_mapping(upper_value, lowercase_after_uppercase),
            Ok(false)
        );
        assert_eq!(
            store.is_member_of_string_mapping(lone_upper, uppercase_after_lowercase),
            Ok(true)
        );
        assert_eq!(
            store.is_member_of_string_mapping(lone_lower, uppercase_after_lowercase),
            Ok(false)
        );
    }

    #[test]
    fn template_intersection_placeholders_ignore_the_canonical_empty_object() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let empty_type_literal = bootstrap.empty_type_literal_type;
        let intersection = store
            .alloc_intersection_type(ObjectFlags::NONE, vec![number, empty_type_literal])
            .unwrap();
        let pattern = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[intersection])
            .unwrap();
        let valid = string_literal(&mut store, "id-42");
        let invalid = string_literal(&mut store, "id-value");

        assert_eq!(
            store.is_type_matched_by_template_literal_type(valid, pattern),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(invalid, pattern),
            Ok(false)
        );
    }

    #[test]
    fn template_and_mapping_patterns_remove_covered_string_literal_union_members() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let pattern = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();
        let covered = string_literal(&mut store, "do-save");
        let uncovered = string_literal(&mut store, "ns:thing");
        let uppercase_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let uppercase = store
            .get_string_mapping_type(uppercase_symbol, string)
            .unwrap();
        let upper_value = string_literal(&mut store, "SAVE");
        let mixed_value = string_literal(&mut store, "Save");

        assert_eq!(
            store.template_result_union(&[covered, pattern]),
            Ok(pattern)
        );
        assert_eq!(
            store.template_result_union(&[upper_value, uppercase]),
            Ok(uppercase)
        );

        let uncovered_union = store.template_result_union(&[uncovered, pattern]).unwrap();
        let Some(TypeData::Union(union)) =
            store.type_payload(uncovered_union).map(TypeRecord::data)
        else {
            panic!("nonmatching literals must remain in the template union")
        };
        assert!(union.union.types.contains(&uncovered));
        assert!(union.union.types.contains(&pattern));

        let mixed_union = store
            .template_result_union(&[mixed_value, uppercase])
            .unwrap();
        let Some(TypeData::Union(union)) = store.type_payload(mixed_union).map(TypeRecord::data)
        else {
            panic!("nonmatching literals must remain in the intrinsic mapping union")
        };
        assert!(union.union.types.contains(&mixed_value));
        assert!(union.union.types.contains(&uppercase));
    }

    #[test]
    fn adjacent_template_placeholders_consume_one_encoded_code_point() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let pattern = store
            .get_template_literal_type(
                &[String::new(), String::new(), String::new()],
                &[string, number],
            )
            .unwrap();
        let emoji = string_literal(&mut store, "\u{1f600}42");
        let encoded = encode_js_string(&JsString::from_units(vec![
            0xd800,
            u16::from(b'4'),
            u16::from(b'2'),
        ]));
        let lone = string_literal(&mut store, &encoded);
        let invalid = string_literal(&mut store, "\u{1f600}no");

        assert_eq!(
            store.is_type_matched_by_template_literal_type(emoji, pattern),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(lone, pattern),
            Ok(true)
        );
        assert_eq!(
            store.is_type_matched_by_template_literal_type(invalid, pattern),
            Ok(false)
        );
    }

    #[test]
    fn intrinsic_casing_preserves_surrogate_units_and_unicode_special_cases() {
        let high = encode_js_string(&JsString::from_units(vec![0xd800]));
        let surrounded = encode_js_string(&JsString::from_units(vec![
            u16::from(b'A'),
            0xd800,
            u16::from(b'B'),
        ]));
        let low_prefix = encode_js_string(&JsString::from_units(vec![0xdc00, u16::from(b'x')]));

        assert_eq!(
            decode_js_string(&StringMappingKind::Uppercase.apply(&high)).as_units(),
            &[0xd800]
        );
        assert_eq!(
            decode_js_string(&StringMappingKind::Lowercase.apply(&surrounded)).as_units(),
            &[u16::from(b'a'), 0xd800, u16::from(b'b')]
        );
        assert_eq!(
            decode_js_string(&StringMappingKind::Capitalize.apply(&low_prefix)).as_units(),
            &[0xdc00, u16::from(b'x')]
        );
        assert_eq!(StringMappingKind::Uppercase.apply("\u{00df}foo"), "SSFOO");
        assert_eq!(StringMappingKind::Uppercase.apply("\u{fb01}oo"), "FIOO");
        assert_eq!(
            StringMappingKind::Lowercase.apply("\u{0130}SPANYOL"),
            "i\u{0307}spanyol"
        );
        assert_eq!(
            StringMappingKind::Lowercase.apply("\u{039f}\u{03a3}"),
            "\u{03bf}\u{03c2}"
        );
        assert_eq!(
            StringMappingKind::Lowercase.apply("\u{1c89}\u{03a3}"),
            "\u{1c89}\u{03c3}"
        );
    }

    #[test]
    fn intrinsic_lowercase_preserves_final_sigma_around_existing_cased_characters() {
        for character in ['\u{019B}', '\u{0264}', '\u{A7D3}', '\u{A7D5}'] {
            assert_eq!(
                StringMappingKind::Lowercase.apply(&format!("{character}\u{03a3}")),
                format!("{character}\u{03c2}"),
            );
            assert_eq!(
                StringMappingKind::Lowercase.apply(&format!("A\u{03a3}{character}")),
                format!("a\u{03c3}{character}"),
            );
            assert_eq!(
                StringMappingKind::Uppercase.apply(&character.to_string()),
                character.to_string(),
            );
        }

        let lone = encode_js_string(&JsString::from_units(vec![u16::from(b'A'), 0xd800, 0x03a3]));
        assert_eq!(
            decode_js_string(&StringMappingKind::Lowercase.apply(&lone)).as_units(),
            &[u16::from(b'a'), 0xd800, 0x03c3],
        );
    }

    #[test]
    fn intrinsic_union_mapping_removes_duplicate_transformed_literals() {
        let mut store = initialized_store();
        let upper = store
            .get_template_literal_type(&["A".to_owned()], &[])
            .unwrap();
        let lower = store
            .get_template_literal_type(&["a".to_owned()], &[])
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![upper, lower])
            .unwrap();
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );

        let result = store.get_string_mapping_type(symbol, union).unwrap();
        assert_eq!(result, upper);
        let Some(TypeData::Literal(literal)) = store.type_payload(result).map(TypeRecord::data)
        else {
            panic!("duplicate uppercase results must reduce to one canonical literal")
        };
        assert_eq!(literal.value, LiteralValue::String("A".to_owned()));
    }

    #[test]
    fn intrinsic_union_mappings_preserve_exact_unicode_special_casing_keys() {
        let mut store = initialized_store();
        let cases = [
            (
                "Lowercase",
                ["\u{0130}SPANYOL", "\u{039f}\u{03a3}"],
                ["i\u{0307}spanyol", "\u{03bf}\u{03c2}"],
            ),
            (
                "Uppercase",
                ["\u{00df}foo", "\u{fb01}oo"],
                ["SSFOO", "FIOO"],
            ),
            (
                "Capitalize",
                ["\u{00df}foo", "\u{fb01}oo"],
                ["SSfoo", "FIoo"],
            ),
            (
                "Uncapitalize",
                ["\u{0130}foo", "\u{039f}\u{03a3}"],
                ["i\u{0307}foo", "\u{03bf}\u{03a3}"],
            ),
        ];

        for (name, inputs, expected) in cases {
            let symbol = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source(name),
                CheckFlags::NONE,
            );
            let input_types = inputs
                .iter()
                .map(|value| string_literal(&mut store, value))
                .collect::<Vec<_>>();
            let union = store.template_result_union(&input_types).unwrap();
            let mapped = store.get_string_mapping_type(symbol, union).unwrap();
            let Some(TypeData::Union(mapped)) = store.type_payload(mapped).map(TypeRecord::data)
            else {
                panic!("{name} must retain both distinct mapped property keys")
            };
            let mut actual = mapped
                .union
                .types
                .iter()
                .map(
                    |type_| match store.type_payload(*type_).map(TypeRecord::data) {
                        Some(TypeData::Literal(literal)) => match &literal.value {
                            LiteralValue::String(value) => value.as_str(),
                            _ => panic!("{name} must produce string literal keys"),
                        },
                        _ => panic!("{name} must produce string literal keys"),
                    },
                )
                .collect::<Vec<_>>();
            actual.sort_unstable();
            let mut expected = expected;
            expected.sort_unstable();
            assert_eq!(actual, expected, "{name} property keys");
        }
    }

    #[test]
    fn cached_template_and_mapping_lookups_remain_read_only() {
        let mut store = initialized_store();
        let value = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let texts = ["prefix-".to_owned(), String::new()];
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let before = store.type_len();

        assert_eq!(
            store.cached_resolved_template_literal_type(&texts, &[value]),
            Ok(None)
        );
        assert_eq!(
            store.cached_resolved_string_mapping_type(symbol, value),
            Ok(None)
        );
        assert_eq!(store.type_len(), before);

        let template = store.get_template_literal_type(&texts, &[value]).unwrap();
        let mapping = store.get_string_mapping_type(symbol, value).unwrap();
        let warm = store.type_len();
        assert_eq!(
            store.cached_resolved_template_literal_type(&texts, &[value]),
            Ok(Some(template))
        );
        assert_eq!(
            store.cached_resolved_string_mapping_type(symbol, value),
            Ok(Some(mapping))
        );
        assert_eq!(store.type_len(), warm);
    }

    #[test]
    fn broad_string_absorbs_template_and_intrinsic_mapping_union_members() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let literal = store
            .get_template_literal_type(&["literal".to_owned()], &[])
            .unwrap();
        let template = store
            .get_template_literal_type(&["prefix-".to_owned(), String::new()], &[number])
            .unwrap();
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let mapping = store.get_string_mapping_type(symbol, string).unwrap();
        let count = store.type_len();

        assert_eq!(
            store.cached_template_result_union(&[literal, template, mapping, string]),
            Ok(Some(string))
        );
        assert_eq!(
            store.template_result_union(&[literal, template, mapping, string]),
            Ok(string)
        );
        assert_eq!(store.type_len(), count);
    }

    #[test]
    fn wildcard_error_and_unknown_reduce_template_unions_by_bootstrap_identity() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let error = bootstrap.error_type;
        let wildcard = bootstrap.wildcard_type;
        let unknown = bootstrap.unknown_type;
        let number = bootstrap.number_type;
        let pattern = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[number])
            .unwrap();
        let count = store.type_len();

        assert_eq!(
            store.template_result_union(&[pattern, unknown]),
            Ok(unknown)
        );
        assert_eq!(store.template_result_union(&[pattern, any]), Ok(any));
        assert_eq!(
            store.template_result_union(&[pattern, any, error]),
            Ok(error)
        );
        assert_eq!(
            store.template_result_union(&[pattern, error, wildcard]),
            Ok(wildcard)
        );
        assert_eq!(store.type_len(), count);
    }

    #[test]
    fn cached_distributed_templates_find_existing_literal_unions_without_writes() {
        let mut store = initialized_store();
        let first = store
            .get_template_literal_type(&["first".to_owned()], &[])
            .unwrap();
        let second = store
            .get_template_literal_type(&["second".to_owned()], &[])
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![first, second])
            .unwrap();
        let texts = ["id-".to_owned(), String::new()];
        let count = store.type_len();

        assert_eq!(
            store.cached_resolved_template_literal_type(&texts, &[union]),
            Ok(None)
        );
        assert_eq!(store.type_len(), count);

        let distributed = store.get_template_literal_type(&texts, &[union]).unwrap();
        let warm = store.type_len();
        assert_eq!(
            store.cached_resolved_template_literal_type(&texts, &[union]),
            Ok(Some(distributed))
        );
        assert_eq!(store.type_len(), warm);
    }

    #[test]
    fn large_template_products_saturate_before_expansion_or_allocation() {
        let mut store = initialized_store();
        let constituents = (0..10)
            .map(|index| {
                store
                    .get_template_literal_type(&[index.to_string()], &[])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let union = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, constituents)
            .unwrap();
        let placeholders = vec![union; 32];
        let texts = vec![String::new(); placeholders.len() + 1];
        let before = store.type_len();

        assert_eq!(
            store.get_template_cross_product_union_size(&placeholders),
            Ok(usize::MAX)
        );
        assert_eq!(
            store.get_template_literal_type(&texts, &placeholders),
            Err(TemplateTypeError::CrossProductTooLarge {
                size: usize::MAX,
                limit: MAX_TEMPLATE_UNION_SIZE,
            })
        );
        assert_eq!(store.type_len(), before);
    }
}
