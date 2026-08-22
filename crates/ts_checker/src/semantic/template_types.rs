//! Canonical template-literal construction and intrinsic string mappings.
//!
//! The algorithms follow `getTemplateLiteralType`, `getStringMappingType`,
//! and `checkCrossProductUnion` in the pinned upstream checker.

use std::{cmp::Ordering, collections::HashSet, fmt};

use ts_binder::SemanticSymbolId;

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
                let Some(first) = value.chars().next() else {
                    return String::new();
                };
                let first_text = &value[..first.len_utf8()];
                let mut result = match self {
                    Self::Capitalize => javascript_uppercase(first_text),
                    Self::Uncapitalize => javascript_lowercase(first_text),
                    Self::Uppercase | Self::Lowercase => unreachable!(),
                };
                result.push_str(&value[first.len_utf8()..]);
                result
            }
        }
    }
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
        if has_post_unicode_15_case_mapping(character) {
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
        let symbol_record = self
            .symbol(symbol)
            .ok_or(TemplateTypeError::InvalidMappingSymbol(symbol))?;
        let kind = symbol_record
            .name()
            .as_utf8()
            .and_then(StringMappingKind::from_name)
            .ok_or(TemplateTypeError::UnsupportedMappingSymbol(symbol))?;
        if self.type_payload(target).is_none() {
            return Err(TemplateTypeError::InvalidType(target));
        }
        self.get_string_mapping_type_worker(symbol, kind, target)
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
                normalized
                    .current
                    .push_str(&Self::template_string_for_type(type_, record)?);
                normalized.current.push_str(&texts[index + 1]);
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
                normalized.current.push_str(&template.texts[0]);
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
                normalized.current.push_str(&texts[index + 1]);
            } else if self.is_template_generic_index_type(type_, &mut HashSet::new())?
                || self.is_template_pattern_placeholder(type_, &mut HashSet::new())?
            {
                normalized.types.push(type_);
                normalized
                    .texts
                    .push(std::mem::take(&mut normalized.current));
                normalized.current.push_str(&texts[index + 1]);
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
        if let Some(existing) = self.types().find_map(|(id, record)| match record.data() {
            TypeData::StringMapping(mapping)
                if record.symbol() == Some(symbol) && mapping.target == target =>
            {
                Some(id)
            }
            _ => None,
        }) {
            return Ok(existing);
        }
        if !self.try_reserve_types(1) {
            return Err(TemplateTypeError::Capacity);
        }
        self.alloc_string_mapping_type(Some(symbol), target)
            .ok_or(TemplateTypeError::Capacity)
    }

    fn template_result_union(&mut self, types: &[TypeId]) -> Result<TypeId, TemplateTypeError> {
        let never = self
            .intrinsic_bootstrap()
            .ok_or(TemplateTypeError::BootstrapUninitialized)?
            .never_type;
        let mut flattened = Vec::with_capacity(types.len());
        self.flatten_template_union_types(types, &mut flattened, &mut HashSet::new())?;
        flattened.retain(|type_| {
            self.type_payload(*type_)
                .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
        });
        flattened.sort_by(|left, right| self.compare_template_union_types(*left, *right));
        flattened.dedup();
        match flattened.as_slice() {
            [] => return Ok(never),
            [single] => return Ok(*single),
            _ => {}
        }

        if flattened
            .iter()
            .all(|type_| self.validate_union_constituent(*type_).is_ok())
        {
            let mut prepared = self.prepare_type_query_types(&[], &[], &[], 1, 0)?;
            return self
                .literal_union_type_prepared(&flattened, None, &mut prepared)
                .map_err(Into::into);
        }

        if let Some(existing) = self.types().find_map(|(id, record)| match record.data() {
            TypeData::Union(union)
                if record.alias().is_none()
                    && union.origin.is_none()
                    && union.union.types == flattened =>
            {
                Some(id)
            }
            _ => None,
        }) {
            return Ok(existing);
        }

        if !self.try_reserve_types(1) {
            return Err(TemplateTypeError::Capacity);
        }
        self.alloc_union_type(ObjectFlags::NONE, flattened)
            .ok_or(TemplateTypeError::Capacity)
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
