//! Newtype macros for Go integer flag and enum types.
//!
//! `go_flags!` makes a bit set. `go_enum!` makes a plain Go enum. Both keep
//! the Go numeric values, so tables and switches port one to one.
//!
//! Both are `#[macro_export]` in `goport_util`. `ts_goport` files import
//! them from `crate::flags_macros` (an inline module in its `lib.rs`).

#[macro_export]
macro_rules! go_flags {
    ($name:ident, $repr:ty { $($(#[$meta:meta])* $konst:ident = $value:expr;)* }) => {
        #[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub $repr);

        #[allow(non_upper_case_globals)]
        impl $name {
            $($(#[$meta])* pub const $konst: Self = Self($value as $repr);)*

            #[must_use]
            pub const fn bits(self) -> $repr {
                self.0
            }

            /// Go `x&y != 0`.
            #[must_use]
            pub const fn intersects(self, other: Self) -> bool {
                self.0 & other.0 != 0
            }

            /// Go `x&y == y`.
            #[must_use]
            pub const fn contains(self, other: Self) -> bool {
                self.0 & other.0 == other.0
            }

            #[must_use]
            pub const fn is_empty(self) -> bool {
                self.0 == 0
            }

            /// Go `x &^ y`.
            #[must_use]
            pub const fn without(self, other: Self) -> Self {
                Self(self.0 & !other.0)
            }

            #[must_use]
            pub const fn union(self, other: Self) -> Self {
                Self(self.0 | other.0)
            }
        }

        impl std::ops::BitOr for $name {
            type Output = Self;
            fn bitor(self, rhs: Self) -> Self {
                Self(self.0 | rhs.0)
            }
        }

        impl std::ops::BitOrAssign for $name {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl std::ops::BitAnd for $name {
            type Output = Self;
            fn bitand(self, rhs: Self) -> Self {
                Self(self.0 & rhs.0)
            }
        }

        impl std::ops::BitAndAssign for $name {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl std::ops::Not for $name {
            type Output = Self;
            fn not(self) -> Self {
                Self(!self.0)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({:#x})", stringify!($name), self.0)
            }
        }
    };
}

#[macro_export]
macro_rules! go_enum {
    ($name:ident, $repr:ty { $($(#[$meta:meta])* $konst:ident = $value:expr;)* }) => {
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub $repr);

        #[allow(non_upper_case_globals)]
        impl $name {
            $($(#[$meta])* pub const $konst: Self = Self($value as $repr);)*
        }
    };
}
