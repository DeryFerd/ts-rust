use std::{fmt, ops};

macro_rules! impl_flag_operators {
    ($flags:ty) => {
        impl ops::BitAnd for $flags {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }

        impl ops::BitAndAssign for $flags {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl ops::BitOr for $flags {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }

        impl ops::BitOrAssign for $flags {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl ops::BitXor for $flags {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self::Output {
                Self(self.0 ^ rhs.0)
            }
        }

        impl ops::Not for $flags {
            type Output = Self;

            fn not(self) -> Self::Output {
                Self(!self.0)
            }
        }
    };
}

/// Canonical semantic type flags.
///
/// These values are pinned to typescript-go
/// `internal/checker/types.go` at
/// `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Their numeric order is
/// observable: upstream uses it to order union constituents and to enable
/// early exits while relating unions.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeFlags(u32);

impl TypeFlags {
    pub const NONE: Self = Self(0);
    pub const ANY: Self = Self(1 << 0);
    pub const UNKNOWN: Self = Self(1 << 1);
    pub const UNDEFINED: Self = Self(1 << 2);
    pub const NULL: Self = Self(1 << 3);
    pub const VOID: Self = Self(1 << 4);
    pub const STRING: Self = Self(1 << 5);
    pub const NUMBER: Self = Self(1 << 6);
    pub const BIG_INT: Self = Self(1 << 7);
    pub const BOOLEAN: Self = Self(1 << 8);
    pub const ES_SYMBOL: Self = Self(1 << 9);
    pub const STRING_LITERAL: Self = Self(1 << 10);
    pub const NUMBER_LITERAL: Self = Self(1 << 11);
    pub const BIG_INT_LITERAL: Self = Self(1 << 12);
    pub const BOOLEAN_LITERAL: Self = Self(1 << 13);
    pub const UNIQUE_ES_SYMBOL: Self = Self(1 << 14);
    pub const ENUM_LITERAL: Self = Self(1 << 15);
    pub const ENUM: Self = Self(1 << 16);
    pub const NON_PRIMITIVE: Self = Self(1 << 17);
    pub const NEVER: Self = Self(1 << 18);
    pub const TYPE_PARAMETER: Self = Self(1 << 19);
    pub const OBJECT: Self = Self(1 << 20);
    pub const INDEX: Self = Self(1 << 21);
    pub const TEMPLATE_LITERAL: Self = Self(1 << 22);
    pub const STRING_MAPPING: Self = Self(1 << 23);
    pub const SUBSTITUTION: Self = Self(1 << 24);
    pub const INDEXED_ACCESS: Self = Self(1 << 25);
    pub const CONDITIONAL: Self = Self(1 << 26);
    pub const UNION: Self = Self(1 << 27);
    pub const INTERSECTION: Self = Self(1 << 28);
    pub const RESERVED_1: Self = Self(1 << 29);
    pub const RESERVED_2: Self = Self(1 << 30);
    pub const RESERVED_3: Self = Self(1 << 31);

    pub const ANY_OR_UNKNOWN: Self = Self(Self::ANY.0 | Self::UNKNOWN.0);
    pub const NULLABLE: Self = Self(Self::UNDEFINED.0 | Self::NULL.0);
    pub const LITERAL: Self = Self(
        Self::STRING_LITERAL.0
            | Self::NUMBER_LITERAL.0
            | Self::BIG_INT_LITERAL.0
            | Self::BOOLEAN_LITERAL.0,
    );
    pub const UNIT: Self =
        Self(Self::ENUM.0 | Self::LITERAL.0 | Self::UNIQUE_ES_SYMBOL.0 | Self::NULLABLE.0);
    pub const FRESHABLE: Self = Self(Self::ENUM.0 | Self::LITERAL.0);
    pub const STRING_OR_NUMBER_LITERAL: Self =
        Self(Self::STRING_LITERAL.0 | Self::NUMBER_LITERAL.0);
    pub const STRING_OR_NUMBER_LITERAL_OR_UNIQUE: Self =
        Self(Self::STRING_LITERAL.0 | Self::NUMBER_LITERAL.0 | Self::UNIQUE_ES_SYMBOL.0);
    pub const DEFINITELY_FALSY: Self = Self(
        Self::STRING_LITERAL.0
            | Self::NUMBER_LITERAL.0
            | Self::BIG_INT_LITERAL.0
            | Self::BOOLEAN_LITERAL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0,
    );
    pub const POSSIBLY_FALSY: Self = Self(
        Self::DEFINITELY_FALSY.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BIG_INT.0
            | Self::BOOLEAN.0,
    );
    pub const INTRINSIC: Self = Self(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BIG_INT.0
            | Self::ES_SYMBOL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0
            | Self::NEVER.0
            | Self::NON_PRIMITIVE.0,
    );
    pub const STRING_LIKE: Self = Self(
        Self::STRING.0 | Self::STRING_LITERAL.0 | Self::TEMPLATE_LITERAL.0 | Self::STRING_MAPPING.0,
    );
    pub const NUMBER_LIKE: Self = Self(Self::NUMBER.0 | Self::NUMBER_LITERAL.0 | Self::ENUM.0);
    pub const BIG_INT_LIKE: Self = Self(Self::BIG_INT.0 | Self::BIG_INT_LITERAL.0);
    pub const BOOLEAN_LIKE: Self = Self(Self::BOOLEAN.0 | Self::BOOLEAN_LITERAL.0);
    pub const ENUM_LIKE: Self = Self(Self::ENUM.0 | Self::ENUM_LITERAL.0);
    pub const ES_SYMBOL_LIKE: Self = Self(Self::ES_SYMBOL.0 | Self::UNIQUE_ES_SYMBOL.0);
    pub const VOID_LIKE: Self = Self(Self::VOID.0 | Self::UNDEFINED.0);
    pub const PRIMITIVE: Self = Self(
        Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ENUM_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::VOID_LIKE.0
            | Self::NULL.0,
    );
    pub const DEFINITELY_NON_NULLABLE: Self = Self(
        Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ENUM_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::OBJECT.0
            | Self::NON_PRIMITIVE.0,
    );
    pub const DISJOINT_DOMAINS: Self = Self(
        Self::NON_PRIMITIVE.0
            | Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::VOID_LIKE.0
            | Self::NULL.0,
    );
    pub const UNION_OR_INTERSECTION: Self = Self(Self::UNION.0 | Self::INTERSECTION.0);
    pub const STRUCTURED_TYPE: Self = Self(Self::OBJECT.0 | Self::UNION.0 | Self::INTERSECTION.0);
    pub const TYPE_VARIABLE: Self = Self(Self::TYPE_PARAMETER.0 | Self::INDEXED_ACCESS.0);
    pub const INSTANTIABLE_NON_PRIMITIVE: Self =
        Self(Self::TYPE_VARIABLE.0 | Self::CONDITIONAL.0 | Self::SUBSTITUTION.0);
    pub const INSTANTIABLE_PRIMITIVE: Self =
        Self(Self::INDEX.0 | Self::TEMPLATE_LITERAL.0 | Self::STRING_MAPPING.0);
    pub const INSTANTIABLE: Self =
        Self(Self::INSTANTIABLE_NON_PRIMITIVE.0 | Self::INSTANTIABLE_PRIMITIVE.0);
    pub const STRUCTURED_OR_INSTANTIABLE: Self =
        Self(Self::STRUCTURED_TYPE.0 | Self::INSTANTIABLE.0);
    pub const OBJECT_FLAGS_TYPE: Self = Self(
        Self::ANY.0
            | Self::NULLABLE.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::UNION.0
            | Self::INTERSECTION.0,
    );
    pub const SIMPLIFIABLE: Self =
        Self(Self::INDEXED_ACCESS.0 | Self::CONDITIONAL.0 | Self::INDEX.0);
    pub const SINGLETON: Self = Self(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BOOLEAN.0
            | Self::BIG_INT.0
            | Self::ES_SYMBOL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0
            | Self::NEVER.0
            | Self::NON_PRIMITIVE.0,
    );
    pub const NARROWABLE: Self = Self(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRUCTURED_OR_INSTANTIABLE.0
            | Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ES_SYMBOL.0
            | Self::UNIQUE_ES_SYMBOL.0
            | Self::NON_PRIMITIVE.0,
    );
    pub const INCLUDES_MASK: Self = Self(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::PRIMITIVE.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::UNION.0
            | Self::INTERSECTION.0
            | Self::NON_PRIMITIVE.0
            | Self::TEMPLATE_LITERAL.0
            | Self::STRING_MAPPING.0,
    );
    pub const INCLUDES_MISSING_TYPE: Self = Self::TYPE_PARAMETER;
    pub const INCLUDES_NON_WIDENING_TYPE: Self = Self::INDEX;
    pub const INCLUDES_WILDCARD: Self = Self::INDEXED_ACCESS;
    pub const INCLUDES_EMPTY_OBJECT: Self = Self::CONDITIONAL;
    pub const INCLUDES_INSTANTIABLE: Self = Self::SUBSTITUTION;
    pub const INCLUDES_CONSTRAINED_TYPE_VARIABLE: Self = Self::RESERVED_1;
    pub const INCLUDES_ERROR: Self = Self::RESERVED_2;
    pub const NOT_PRIMITIVE_UNION: Self = Self(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::VOID.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::INTERSECTION.0
            | Self::INCLUDES_INSTANTIABLE.0,
    );

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

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns individual upstream flag names in numeric order.
    #[must_use]
    pub fn names(self) -> Vec<&'static str> {
        let mut result = TYPE_FLAG_NAMES
            .iter()
            .filter_map(|(flag, name)| self.intersects(*flag).then_some(*name))
            .collect::<Vec<_>>();
        if result.is_empty() {
            result.push("None");
        }
        result
    }
}

impl_flag_operators!(TypeFlags);

impl fmt::Display for TypeFlags {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.names().join("|"))
    }
}

const TYPE_FLAG_NAMES: [(TypeFlags, &str); 29] = [
    (TypeFlags::ANY, "Any"),
    (TypeFlags::UNKNOWN, "Unknown"),
    (TypeFlags::UNDEFINED, "Undefined"),
    (TypeFlags::NULL, "Null"),
    (TypeFlags::VOID, "Void"),
    (TypeFlags::STRING, "String"),
    (TypeFlags::NUMBER, "Number"),
    (TypeFlags::BIG_INT, "BigInt"),
    (TypeFlags::BOOLEAN, "Boolean"),
    (TypeFlags::ES_SYMBOL, "ESSymbol"),
    (TypeFlags::STRING_LITERAL, "StringLiteral"),
    (TypeFlags::NUMBER_LITERAL, "NumberLiteral"),
    (TypeFlags::BIG_INT_LITERAL, "BigIntLiteral"),
    (TypeFlags::BOOLEAN_LITERAL, "BooleanLiteral"),
    (TypeFlags::UNIQUE_ES_SYMBOL, "UniqueESSymbol"),
    (TypeFlags::ENUM_LITERAL, "EnumLiteral"),
    (TypeFlags::ENUM, "Enum"),
    (TypeFlags::NON_PRIMITIVE, "NonPrimitive"),
    (TypeFlags::NEVER, "Never"),
    (TypeFlags::TYPE_PARAMETER, "TypeParameter"),
    (TypeFlags::OBJECT, "Object"),
    (TypeFlags::INDEX, "Index"),
    (TypeFlags::TEMPLATE_LITERAL, "TemplateLiteral"),
    (TypeFlags::STRING_MAPPING, "StringMapping"),
    (TypeFlags::SUBSTITUTION, "Substitution"),
    (TypeFlags::INDEXED_ACCESS, "IndexedAccess"),
    (TypeFlags::CONDITIONAL, "Conditional"),
    (TypeFlags::UNION, "Union"),
    (TypeFlags::INTERSECTION, "Intersection"),
];

/// Additional flags carried by canonical semantic types.
///
/// Several bit positions intentionally have different meanings depending on
/// the owning [`TypeFlags`]. Callers must test the type kind before interpreting
/// a reused object bit.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ObjectFlags(u32);

impl ObjectFlags {
    pub const NONE: Self = Self(0);
    pub const CLASS: Self = Self(1 << 0);
    pub const INTERFACE: Self = Self(1 << 1);
    pub const REFERENCE: Self = Self(1 << 2);
    pub const TUPLE: Self = Self(1 << 3);
    pub const ANONYMOUS: Self = Self(1 << 4);
    pub const MAPPED: Self = Self(1 << 5);
    pub const INSTANTIATED: Self = Self(1 << 6);
    pub const OBJECT_LITERAL: Self = Self(1 << 7);
    pub const EVOLVING_ARRAY: Self = Self(1 << 8);
    pub const OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES: Self = Self(1 << 9);
    pub const REVERSE_MAPPED: Self = Self(1 << 10);
    pub const JSX_ATTRIBUTES: Self = Self(1 << 11);
    pub const JS_LITERAL: Self = Self(1 << 12);
    pub const FRESH_LITERAL: Self = Self(1 << 13);
    pub const ARRAY_LITERAL: Self = Self(1 << 14);
    pub const PRIMITIVE_UNION: Self = Self(1 << 15);
    pub const CONTAINS_WIDENING_TYPE: Self = Self(1 << 16);
    pub const CONTAINS_OBJECT_OR_ARRAY_LITERAL: Self = Self(1 << 17);
    pub const NON_INFERRABLE_TYPE: Self = Self(1 << 18);
    pub const COULD_CONTAIN_TYPE_VARIABLES_COMPUTED: Self = Self(1 << 19);
    pub const COULD_CONTAIN_TYPE_VARIABLES: Self = Self(1 << 20);
    pub const MEMBERS_RESOLVED: Self = Self(1 << 21);

    pub const CLASS_OR_INTERFACE: Self = Self(Self::CLASS.0 | Self::INTERFACE.0);
    pub const REQUIRES_WIDENING: Self =
        Self(Self::CONTAINS_WIDENING_TYPE.0 | Self::CONTAINS_OBJECT_OR_ARRAY_LITERAL.0);
    pub const PROPAGATING_FLAGS: Self = Self(
        Self::CONTAINS_WIDENING_TYPE.0
            | Self::CONTAINS_OBJECT_OR_ARRAY_LITERAL.0
            | Self::NON_INFERRABLE_TYPE.0,
    );
    pub const INSTANTIATED_MAPPED: Self = Self(Self::MAPPED.0 | Self::INSTANTIATED.0);

    // Meanings requiring TypeFlags::OBJECT.
    pub const CONTAINS_SPREAD: Self = Self(1 << 22);
    pub const OBJECT_REST_TYPE: Self = Self(1 << 23);
    pub const INSTANTIATION_EXPRESSION_TYPE: Self = Self(1 << 24);
    pub const SINGLE_SIGNATURE_TYPE: Self = Self(1 << 25);
    pub const IS_CLASS_INSTANCE_CLONE: Self = Self(1 << 26);
    // Meanings requiring TypeFlags::OBJECT and ObjectFlags::REFERENCE.
    pub const IDENTICAL_BASE_TYPE_CALCULATED: Self = Self(1 << 27);
    pub const IDENTICAL_BASE_TYPE_EXISTS: Self = Self(1 << 28);
    pub const UNRESOLVED_MEMBERS: Self = Self(1 << 29);
    pub const FROM_TYPE_NODE: Self = Self(1 << 30);

    pub const OBJECT_TYPE_KIND_MASK: Self = Self(
        Self::CLASS_OR_INTERFACE.0
            | Self::REFERENCE.0
            | Self::TUPLE.0
            | Self::ANONYMOUS.0
            | Self::MAPPED.0
            | Self::REVERSE_MAPPED.0
            | Self::EVOLVING_ARRAY.0
            | Self::INSTANTIATION_EXPRESSION_TYPE.0
            | Self::SINGLE_SIGNATURE_TYPE.0,
    );

    // Reused meanings requiring union/intersection or substitution TypeFlags.
    pub const IS_GENERIC_TYPE_COMPUTED: Self = Self(1 << 22);
    pub const IS_GENERIC_OBJECT_TYPE: Self = Self(1 << 23);
    pub const IS_GENERIC_INDEX_TYPE: Self = Self(1 << 24);
    pub const IS_GENERIC_TYPE: Self =
        Self(Self::IS_GENERIC_OBJECT_TYPE.0 | Self::IS_GENERIC_INDEX_TYPE.0);
    // Reused meanings requiring TypeFlags::UNION.
    pub const CONTAINS_INTERSECTIONS: Self = Self(1 << 25);
    pub const IS_UNKNOWN_LIKE_UNION_COMPUTED: Self = Self(1 << 26);
    pub const IS_UNKNOWN_LIKE_UNION: Self = Self(1 << 27);
    // Reused meanings requiring TypeFlags::INTERSECTION.
    pub const IS_NEVER_INTERSECTION_COMPUTED: Self = Self(1 << 25);
    pub const IS_NEVER_INTERSECTION: Self = Self(1 << 26);
    pub const IS_CONSTRAINED_TYPE_VARIABLE: Self = Self(1 << 27);

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

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl_flag_operators!(ObjectFlags);

#[cfg(test)]
mod tests {
    use super::{ObjectFlags, TypeFlags};

    #[test]
    fn type_flag_bits_match_upstream_and_preserve_sort_order() {
        let individual = [
            TypeFlags::ANY,
            TypeFlags::UNKNOWN,
            TypeFlags::UNDEFINED,
            TypeFlags::NULL,
            TypeFlags::VOID,
            TypeFlags::STRING,
            TypeFlags::NUMBER,
            TypeFlags::BIG_INT,
            TypeFlags::BOOLEAN,
            TypeFlags::ES_SYMBOL,
            TypeFlags::STRING_LITERAL,
            TypeFlags::NUMBER_LITERAL,
            TypeFlags::BIG_INT_LITERAL,
            TypeFlags::BOOLEAN_LITERAL,
            TypeFlags::UNIQUE_ES_SYMBOL,
            TypeFlags::ENUM_LITERAL,
            TypeFlags::ENUM,
            TypeFlags::NON_PRIMITIVE,
            TypeFlags::NEVER,
            TypeFlags::TYPE_PARAMETER,
            TypeFlags::OBJECT,
            TypeFlags::INDEX,
            TypeFlags::TEMPLATE_LITERAL,
            TypeFlags::STRING_MAPPING,
            TypeFlags::SUBSTITUTION,
            TypeFlags::INDEXED_ACCESS,
            TypeFlags::CONDITIONAL,
            TypeFlags::UNION,
            TypeFlags::INTERSECTION,
            TypeFlags::RESERVED_1,
            TypeFlags::RESERVED_2,
            TypeFlags::RESERVED_3,
        ];
        for (bit, flag) in individual.into_iter().enumerate() {
            assert_eq!(flag.bits(), 1_u32 << bit);
        }
        assert!(TypeFlags::INDEXED_ACCESS < TypeFlags::CONDITIONAL);
        assert!(TypeFlags::CONDITIONAL < TypeFlags::UNION);
        assert!(TypeFlags::UNION < TypeFlags::INTERSECTION);
    }

    #[test]
    fn aggregate_type_flags_match_pinned_numeric_values() {
        assert_eq!(TypeFlags::ANY_OR_UNKNOWN.bits(), 0x0000_0003);
        assert_eq!(TypeFlags::NULLABLE.bits(), 0x0000_000c);
        assert_eq!(TypeFlags::LITERAL.bits(), 0x0000_3c00);
        assert_eq!(TypeFlags::PRIMITIVE.bits(), 0x00c1_fffc);
        assert_eq!(TypeFlags::STRUCTURED_TYPE.bits(), 0x1810_0000);
        assert_eq!(TypeFlags::INSTANTIABLE.bits(), 0x07e8_0000);
        assert_eq!(TypeFlags::OBJECT_FLAGS_TYPE.bits(), 0x1814_000d);
        assert_eq!(TypeFlags::INCLUDES_MASK.bits(), 0x18d7_ffff);
        assert_eq!(TypeFlags::NOT_PRIMITIVE_UNION.bits(), 0x1114_0013);
    }

    #[test]
    fn names_match_upstream_order_and_ignore_reserved_bits() {
        assert_eq!(TypeFlags::NONE.names(), ["None"]);
        assert_eq!(
            (TypeFlags::CONDITIONAL | TypeFlags::STRING | TypeFlags::ANY).names(),
            ["Any", "String", "Conditional"]
        );
        assert_eq!(TypeFlags::RESERVED_1.names(), ["None"]);
        assert_eq!(
            (TypeFlags::NUMBER | TypeFlags::NUMBER_LITERAL).to_string(),
            "Number|NumberLiteral"
        );
    }

    #[test]
    fn object_flags_preserve_context_dependent_bit_reuse() {
        assert_eq!(ObjectFlags::CLASS.bits(), 1 << 0);
        assert_eq!(ObjectFlags::MEMBERS_RESOLVED.bits(), 1 << 21);
        assert_eq!(ObjectFlags::FROM_TYPE_NODE.bits(), 1 << 30);
        assert_eq!(
            ObjectFlags::CONTAINS_SPREAD.bits(),
            ObjectFlags::IS_GENERIC_TYPE_COMPUTED.bits()
        );
        assert_eq!(
            ObjectFlags::SINGLE_SIGNATURE_TYPE.bits(),
            ObjectFlags::CONTAINS_INTERSECTIONS.bits()
        );
        assert_eq!(
            ObjectFlags::CONTAINS_INTERSECTIONS.bits(),
            ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED.bits()
        );
        assert!(ObjectFlags::OBJECT_TYPE_KIND_MASK.contains(
            ObjectFlags::CLASS
                | ObjectFlags::REFERENCE
                | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE
        ));
    }
}
