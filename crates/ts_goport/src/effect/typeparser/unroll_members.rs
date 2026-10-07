//! Port of Effect-TS/tsgo `internal/typeparser/unroll_members.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    /// UnrollUnionMembers returns the constituent types of a union type,
    /// or a single-element slice containing the type itself if it's not a union.
    // Go: typeparser/unroll_members.go UnrollUnionMembers
    pub fn unroll_union_members(&mut self, t: TypeId) -> Vec<TypeId> {
        if t.is_nil() {
            return Vec::new();
        }
        if self.checker.ty(t).flags.intersects(TypeFlags::UNION) {
            return self.checker.ty(t).types().to_vec();
        }
        vec![t]
    }
}
