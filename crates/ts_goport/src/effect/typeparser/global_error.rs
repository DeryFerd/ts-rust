// Go: internal/typeparser/global_error.go

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    /// IsGlobalErrorType reports whether the given type is exactly the global Error type.
    /// It performs a bidirectional assignability check to ensure the type is not a subclass
    /// or unrelated type. Types like any and unknown are excluded since they are
    /// bidirectionally assignable to everything and would produce false positives.
    pub fn is_global_error_type(&mut self, t: TypeId) -> bool {
        if t.is_nil() {
            return false;
        }
        cached!(self, is_global_error_type, t, 'compute: {
            // Exclude any/unknown — they are bidirectionally assignable to everything
            if self
                .checker
                .ty(t)
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
            {
                break 'compute false;
            }

            let error_symbol =
                self.checker
                    .resolve_name_exported("Error", Node::NIL, SymbolFlags::TYPE, false);
            if error_symbol.is_nil() {
                break 'compute false;
            }

            let global_error_type = self
                .checker
                .get_declared_type_of_symbol_exported(error_symbol);
            if global_error_type.is_nil() {
                break 'compute false;
            }

            self.checker.is_type_assignable_to(t, global_error_type)
                && self.checker.is_type_assignable_to(global_error_type, t)
        })
    }
}
