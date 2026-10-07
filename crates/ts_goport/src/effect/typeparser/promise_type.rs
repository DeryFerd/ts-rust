// Go: internal/typeparser/promise_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    /// PromiseType returns t when it is the global Promise type or a reference to it.
    /// It intentionally does not match arbitrary thenables or PromiseLike values.
    pub fn promise_type(&mut self, t: TypeId) -> TypeId {
        if t.is_nil() {
            return TypeId::NIL;
        }

        cached!(self, promise_type, t, 'compute: {
            // PORT: Go reads the checker's getGlobalPromiseTypeChecked func
            // field and returns nil when it is nil; the port's field is
            // always set.
            let global_promise_type = self.checker.get_global_promise_type_checked();
            if global_promise_type.is_nil()
                || global_promise_type == self.checker.empty_generic_type
            {
                break 'compute TypeId::NIL;
            }

            if self.checker.is_reference_to_type(t, global_promise_type) || t == global_promise_type
            {
                break 'compute t;
            }

            TypeId::NIL
        })
    }
}
