//! Go `internal/project/programcounter.go`.

use crate::project::prelude::*;

// Go: project/programcounter.go:9 programCounter
// PORT: `mu` is dropped (one thread). Go `map[*compiler.Program]int32` is
// keyed by the program address (PORTING "Programs and checkers"). A Go nil
// map is an empty map.
#[derive(Default)]
pub struct ProgramCounter {
    pub refs: RefCell<FxHashMap<usize, i32>>,
}

// PORT: Go map key `*compiler.Program`.
fn program_key(program: &'static crate::frontend::compiler::NewProgram) -> usize {
    program as *const crate::frontend::compiler::NewProgram as usize
}

impl ProgramCounter {
    // Go: project/programcounter.go:16 Ref
    // Ref increments the reference count for a program. If the program is not
    // yet tracked, it is added with a reference count of 1.
    pub fn ref_(&self, program: &'static crate::frontend::compiler::NewProgram) {
        // Go: `if c.refs == nil { c.refs = make(...) }` (the port map always exists).
        *self
            .refs
            .borrow_mut()
            .entry(program_key(program))
            .or_insert(0) += 1;
    }

    // Go: project/programcounter.go:25 Deref
    pub fn deref(&self, program: &'static crate::frontend::compiler::NewProgram) -> bool {
        let key = program_key(program);
        let mut refs = self.refs.borrow_mut();
        let Some(&count) = refs.get(&key) else {
            return false;
        };
        let count = count - 1;
        if count < 0 {
            panic!("program reference count went below zero");
        }
        if count == 0 {
            refs.remove(&key);
            return true;
        }
        refs.insert(key, count);
        false
    }

    // Go: project/programcounter.go:44 Len
    pub fn len(&self) -> i32 {
        self.refs.borrow().len() as i32
    }
}
