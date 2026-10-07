// Go: internal/typeparser/unique_types_map.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// UniqueTypesResult holds the result of AppendToUniqueTypesMap.
#[derive(Clone, Debug, Default)]
pub struct UniqueTypesResult {
    /// All type indexes encountered (both new and existing)
    pub all_indexes: Vec<String>,
}

impl TypeParser<'_> {
    /// AppendToUniqueTypesMap deduplicates types using bidirectional assignability checks.
    /// It unrolls union types, skips excluded types (via shouldExclude), and for each
    /// remaining type checks if it's already in the memory map. New types get fresh IDs
    /// ("t1", "t2", etc.); known types get their existing IDs.
    /// Returns all indexes encountered (both new and known).
    // PORT: Go ranges over the memory map in random order; the port uses the
    // map's own order. The first equivalent known type wins in both.
    pub fn append_to_unique_types_map(
        &mut self,
        memory: &mut FxHashMap<String, TypeId>,
        initial_type: TypeId,
        mut should_exclude: Option<&mut dyn FnMut(&mut TypeParser<'_>, TypeId) -> bool>,
    ) -> UniqueTypesResult {
        let mut all_indexes: Vec<String> = Vec::new();
        let mut to_test: Vec<TypeId> = vec![initial_type];

        while !to_test.is_empty() {
            // Pop from the end of the slice
            let t = to_test.pop().unwrap_or(TypeId::NIL);

            if t.is_nil() {
                continue;
            }

            if let Some(should_exclude) = should_exclude.as_mut()
                && should_exclude(self, t)
            {
                continue;
            }

            // If it's a union type, expand its members onto the worklist
            if self.checker.ty(t).flags().intersects(TypeFlags::UNION) {
                to_test.extend_from_slice(self.checker.ty(t).types());
                continue;
            }

            // Check if an equivalent type already exists in memory
            let mut matched_id = String::new();
            let known: Vec<(String, TypeId)> = memory
                .iter()
                .map(|(id, &known_type)| (id.clone(), known_type))
                .collect();
            for (type_id, known_type) in known {
                if self.checker.is_type_assignable_to(known_type, t)
                    && self.checker.is_type_assignable_to(t, known_type)
                {
                    matched_id = type_id;
                    break;
                }
            }

            if matched_id.is_empty() {
                // New type: assign a fresh ID
                let new_id = format!("t{}", memory.len() + 1);
                memory.insert(new_id.clone(), t);
                all_indexes.push(new_id);
            } else {
                // Known type: record the existing ID
                all_indexes.push(matched_id);
            }
        }

        UniqueTypesResult { all_indexes }
    }
}
