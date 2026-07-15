//! Byte-exact keys for TypeScript symbol tables.
//!
//! typescript-go reserves invalid UTF-8 byte `0xFE` for compiler-created
//! names. Source names remain ordinary UTF-8 and are never transformed, so a
//! source spelling such as `__call` cannot collide with the internal call key.

use std::{borrow::Borrow, fmt, hash::Hash};

/// The invalid UTF-8 byte that starts typescript-go internal symbol names.
pub const INTERNAL_SYMBOL_NAME_PREFIX: u8 = 0xFE;

const CALL: &[u8] = b"\xFEcall";
const CONSTRUCTOR: &[u8] = b"\xFEconstructor";
const NEW: &[u8] = b"\xFEnew";
const INDEX: &[u8] = b"\xFEindex";
const EXPORT_STAR: &[u8] = b"\xFEexport";
const GLOBAL: &[u8] = b"\xFEglobal";
const MISSING: &[u8] = b"\xFEmissing";
const TYPE: &[u8] = b"\xFEtype";
const OBJECT: &[u8] = b"\xFEobject";
const JSX_ATTRIBUTES: &[u8] = b"\xFEjsxAttributes";
const CLASS: &[u8] = b"\xFEclass";
const FUNCTION: &[u8] = b"\xFEfunction";
const COMPUTED: &[u8] = b"\xFEcomputed";
const ASSIGNMENT_DECLARATION: &[u8] = b"\xFEassignment";
const INSTANTIATION_EXPRESSION: &[u8] = b"\xFEinstantiationExpression";
const IMPORT_ATTRIBUTES: &[u8] = b"\xFEimportAttributes";
const EXPORT_EQUALS: &[u8] = b"export=";
const DEFAULT: &[u8] = b"default";
const THIS: &[u8] = b"this";
const MODULE_EXPORTS: &[u8] = b"module.exports";

/// The complete pinned typescript-go internal symbol-name inventory.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InternalSymbolName {
    Call,
    Constructor,
    New,
    Index,
    ExportStar,
    Global,
    Missing,
    Type,
    Object,
    JsxAttributes,
    Class,
    Function,
    Computed,
    AssignmentDeclaration,
    InstantiationExpression,
    ImportAttributes,
    ExportEquals,
    Default,
    This,
    ModuleExports,
}

impl InternalSymbolName {
    pub const ALL: [Self; 20] = [
        Self::Call,
        Self::Constructor,
        Self::New,
        Self::Index,
        Self::ExportStar,
        Self::Global,
        Self::Missing,
        Self::Type,
        Self::Object,
        Self::JsxAttributes,
        Self::Class,
        Self::Function,
        Self::Computed,
        Self::AssignmentDeclaration,
        Self::InstantiationExpression,
        Self::ImportAttributes,
        Self::ExportEquals,
        Self::Default,
        Self::This,
        Self::ModuleExports,
    ];

    #[must_use]
    pub const fn as_bytes(self) -> &'static [u8] {
        match self {
            Self::Call => CALL,
            Self::Constructor => CONSTRUCTOR,
            Self::New => NEW,
            Self::Index => INDEX,
            Self::ExportStar => EXPORT_STAR,
            Self::Global => GLOBAL,
            Self::Missing => MISSING,
            Self::Type => TYPE,
            Self::Object => OBJECT,
            Self::JsxAttributes => JSX_ATTRIBUTES,
            Self::Class => CLASS,
            Self::Function => FUNCTION,
            Self::Computed => COMPUTED,
            Self::AssignmentDeclaration => ASSIGNMENT_DECLARATION,
            Self::InstantiationExpression => INSTANTIATION_EXPRESSION,
            Self::ImportAttributes => IMPORT_ATTRIBUTES,
            Self::ExportEquals => EXPORT_EQUALS,
            Self::Default => DEFAULT,
            Self::This => THIS,
            Self::ModuleExports => MODULE_EXPORTS,
        }
    }

    #[must_use]
    pub const fn as_ref(self) -> EscapedNameRef<'static> {
        EscapedNameRef {
            bytes: self.as_bytes(),
        }
    }
}

/// An owned byte-exact symbol-table key.
///
/// Construction is restricted to UTF-8 source names, the fixed internal
/// inventory, and validated dynamic-family helpers in [`crate::semantic`].
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EscapedName(Box<[u8]>);

impl Default for EscapedName {
    fn default() -> Self {
        Self::source("")
    }
}

impl EscapedName {
    /// Creates a key from decoded TypeScript source text.
    #[must_use]
    pub fn source(text: impl AsRef<str>) -> Self {
        Self(text.as_ref().as_bytes().into())
    }

    /// Creates one of the fixed compiler-owned keys.
    #[must_use]
    pub fn internal(name: InternalSymbolName) -> Self {
        Self(name.as_bytes().into())
    }

    #[must_use]
    pub const fn as_ref(&self) -> EscapedNameRef<'_> {
        EscapedNameRef { bytes: &self.0 }
    }

    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns the key as UTF-8 only when it has no internal marker.
    #[must_use]
    pub fn as_utf8(&self) -> Option<&str> {
        std::str::from_utf8(&self.0).ok()
    }

    #[must_use]
    pub const fn escaped_display(&self) -> EscapedDisplay<'_> {
        self.as_ref().escaped_display()
    }

    pub(crate) fn private_identifier(global_class_id: u64, description: &str) -> Self {
        let id = global_class_id.to_string();
        let mut bytes = Vec::with_capacity(3 + id.len() + description.len());
        bytes.extend_from_slice(b"\xFE#");
        bytes.extend_from_slice(id.as_bytes());
        bytes.push(b'@');
        bytes.extend_from_slice(description.as_bytes());
        Self(bytes.into_boxed_slice())
    }

    pub(crate) fn known_symbol(symbol_name: &str) -> Self {
        let mut bytes = Vec::with_capacity(2 + symbol_name.len());
        bytes.extend_from_slice(b"\xFE@");
        bytes.extend_from_slice(symbol_name.as_bytes());
        Self(bytes.into_boxed_slice())
    }

    pub(crate) fn unique_symbol(symbol_name: EscapedNameRef<'_>, global_symbol_id: u64) -> Self {
        let id = global_symbol_id.to_string();
        let mut bytes = Vec::with_capacity(3 + symbol_name.as_bytes().len() + id.len());
        bytes.extend_from_slice(b"\xFE@");
        bytes.extend_from_slice(symbol_name.as_bytes());
        bytes.push(b'@');
        bytes.extend_from_slice(id.as_bytes());
        Self(bytes.into_boxed_slice())
    }
}

impl Borrow<[u8]> for EscapedName {
    fn borrow(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl fmt::Debug for EscapedName {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("EscapedName")
            .field(&self.as_bytes())
            .finish()
    }
}

/// A borrowed byte-exact symbol-table key.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EscapedNameRef<'a> {
    bytes: &'a [u8],
}

impl<'a> EscapedNameRef<'a> {
    /// Borrows a decoded source name without allocation.
    #[must_use]
    pub const fn source(text: &'a str) -> Self {
        Self {
            bytes: text.as_bytes(),
        }
    }

    #[must_use]
    pub const fn as_bytes(self) -> &'a [u8] {
        self.bytes
    }

    #[must_use]
    pub fn as_utf8(self) -> Option<&'a str> {
        std::str::from_utf8(self.bytes).ok()
    }

    #[must_use]
    pub fn is_internal(self) -> bool {
        self.bytes.first() == Some(&INTERNAL_SYMBOL_NAME_PREFIX)
    }

    /// Matches pinned `isReservedMemberName` exactly.
    #[must_use]
    pub fn is_reserved_member_name(self) -> bool {
        self.bytes.len() >= 2
            && self.bytes[0] == INTERNAL_SYMBOL_NAME_PREFIX
            && self.bytes[1] != b'@'
            && self.bytes[1] != b'#'
    }

    #[must_use]
    pub fn is_private_identifier(self) -> bool {
        self.bytes.starts_with(b"\xFE#")
    }

    #[must_use]
    pub fn is_late_bound(self) -> bool {
        self.bytes.starts_with(b"\xFE@")
    }

    #[must_use]
    pub fn to_owned(self) -> EscapedName {
        EscapedName(self.bytes.into())
    }

    #[must_use]
    pub const fn escaped_display(self) -> EscapedDisplay<'a> {
        EscapedDisplay(self)
    }
}

impl fmt::Debug for EscapedNameRef<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("EscapedNameRef")
            .field(&self.bytes)
            .finish()
    }
}

/// Explicit, intentionally lossy user-facing rendering of an escaped name.
///
/// Every internal marker becomes `__`, matching pinned typescript-go. The
/// rendered text must never be used for a symbol-table lookup.
#[derive(Clone, Copy, Debug)]
pub struct EscapedDisplay<'a>(EscapedNameRef<'a>);

impl fmt::Display for EscapedDisplay<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bytes = self.0.as_bytes();
        let mut start = 0;
        for (index, byte) in bytes.iter().enumerate() {
            if *byte == INTERNAL_SYMBOL_NAME_PREFIX {
                formatter.write_str(
                    std::str::from_utf8(&bytes[start..index])
                        .expect("EscapedName contains only UTF-8 plus internal markers"),
                )?;
                formatter.write_str("__")?;
                start = index + 1;
            }
        }
        formatter.write_str(
            std::str::from_utf8(&bytes[start..])
                .expect("EscapedName contains only UTF-8 plus internal markers"),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap, HashSet};

    use ts_ast::SyntaxKind;
    use ts_core::SourceText;
    use ts_scanner::ByteScanner;

    use super::{EscapedName, EscapedNameRef, INTERNAL_SYMBOL_NAME_PREFIX, InternalSymbolName};

    #[test]
    fn fixed_inventory_has_exact_bytes_and_display() {
        let expected: [(&[u8], &str); 20] = [
            (b"\xFEcall", "__call"),
            (b"\xFEconstructor", "__constructor"),
            (b"\xFEnew", "__new"),
            (b"\xFEindex", "__index"),
            (b"\xFEexport", "__export"),
            (b"\xFEglobal", "__global"),
            (b"\xFEmissing", "__missing"),
            (b"\xFEtype", "__type"),
            (b"\xFEobject", "__object"),
            (b"\xFEjsxAttributes", "__jsxAttributes"),
            (b"\xFEclass", "__class"),
            (b"\xFEfunction", "__function"),
            (b"\xFEcomputed", "__computed"),
            (b"\xFEassignment", "__assignment"),
            (b"\xFEinstantiationExpression", "__instantiationExpression"),
            (b"\xFEimportAttributes", "__importAttributes"),
            (b"export=", "export="),
            (b"default", "default"),
            (b"this", "this"),
            (b"module.exports", "module.exports"),
        ];
        for (name, (bytes, display)) in InternalSymbolName::ALL.into_iter().zip(expected) {
            assert_eq!(name.as_bytes(), bytes);
            assert_eq!(name.as_ref().escaped_display().to_string(), display);
        }
    }

    #[test]
    fn raw_internal_source_lookalike_and_unicode_thorn_never_collide() {
        assert!(std::str::from_utf8(&[INTERNAL_SYMBOL_NAME_PREFIX]).is_err());
        let source_lookalike = EscapedName::source("__call");
        let unicode_thorn = EscapedName::source("þcall");
        let internal = EscapedName::internal(InternalSymbolName::Call);
        let names = HashSet::from([
            source_lookalike.clone(),
            unicode_thorn.clone(),
            internal.clone(),
        ]);
        assert_eq!(names.len(), 3);
        assert_eq!(source_lookalike.as_bytes(), b"__call");
        assert_eq!(unicode_thorn.as_bytes(), b"\xC3\xBEcall");
        assert_eq!(internal.as_bytes(), b"\xFEcall");
        assert_eq!(source_lookalike.escaped_display().to_string(), "__call");
        assert_eq!(internal.escaped_display().to_string(), "__call");
        assert_eq!(unicode_thorn.escaped_display().to_string(), "þcall");
    }

    #[test]
    fn every_prefixed_internal_name_differs_from_its_source_lookalike() {
        for internal in InternalSymbolName::ALL
            .into_iter()
            .filter(|name| name.as_bytes().starts_with(&[INTERNAL_SYMBOL_NAME_PREFIX]))
        {
            let internal = EscapedName::internal(internal);
            let lookalike = EscapedName::source(internal.escaped_display().to_string());
            assert_ne!(internal, lookalike);
            assert_ne!(internal.as_bytes(), lookalike.as_bytes());
        }
    }

    #[test]
    fn raw_internal_prefix_is_rejected_by_the_source_scanner() {
        let source = SourceText::from_bytes(b"\xFEcall".to_vec());
        let mut scanner = ByteScanner::new(&source);
        let invalid = scanner.scan();
        assert_eq!(invalid.kind, SyntaxKind::Unknown);
        assert_eq!(invalid.text, &[INTERNAL_SYMBOL_NAME_PREFIX]);
        let identifier = scanner.scan();
        assert_eq!(identifier.kind, SyntaxKind::Identifier);
        assert_eq!(identifier.text, b"call");
        assert_eq!(scanner.diagnostics().len(), 1);
    }

    #[test]
    fn raw_byte_order_and_borrowed_lookup_match_go_strings() {
        let source_lookalike = EscapedName::source("__call");
        let unicode_thorn = EscapedName::source("þcall");
        let internal = EscapedName::internal(InternalSymbolName::Call);
        assert!(source_lookalike < unicode_thorn);
        assert!(unicode_thorn < internal);

        let btree = BTreeMap::from([
            (source_lookalike.clone(), 1),
            (unicode_thorn.clone(), 2),
            (internal.clone(), 3),
        ]);
        assert_eq!(btree.get("__call".as_bytes()), Some(&1));
        assert_eq!(btree.get("þcall".as_bytes()), Some(&2));
        assert_eq!(btree.get(InternalSymbolName::Call.as_bytes()), Some(&3));

        let hash = HashMap::from([(source_lookalike, 1), (unicode_thorn, 2), (internal, 3)]);
        assert_eq!(hash.get("__call".as_bytes()), Some(&1));
        assert_eq!(hash.get("þcall".as_bytes()), Some(&2));
        assert_eq!(hash.get(InternalSymbolName::Call.as_bytes()), Some(&3));
    }

    #[test]
    fn reserved_filter_keeps_private_and_symbol_valued_members() {
        let private = EscapedName::private_identifier(7, "#field");
        let known = EscapedName::known_symbol("iterator");
        let unique = EscapedName::unique_symbol(EscapedNameRef::source("token"), 9);
        assert!(InternalSymbolName::Call.as_ref().is_reserved_member_name());
        assert!(!private.as_ref().is_reserved_member_name());
        assert!(!known.as_ref().is_reserved_member_name());
        assert!(!unique.as_ref().is_reserved_member_name());
        assert!(private.as_ref().is_private_identifier());
        assert!(known.as_ref().is_late_bound());
        assert!(unique.as_ref().is_late_bound());
        assert!(!EscapedNameRef::source("__call").is_reserved_member_name());
        assert!(!EscapedNameRef::source("þ").is_reserved_member_name());
        assert!(
            !EscapedNameRef {
                bytes: &[INTERNAL_SYMBOL_NAME_PREFIX],
            }
            .is_reserved_member_name()
        );
        assert_eq!(private.escaped_display().to_string(), "__#7@#field");
        assert_eq!(known.escaped_display().to_string(), "__@iterator");
        assert_eq!(unique.escaped_display().to_string(), "__@token@9");
    }
}
