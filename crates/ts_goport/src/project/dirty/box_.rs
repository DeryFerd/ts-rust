//! Go `internal/project/dirty/box.go`.

use crate::project::dirty::prelude::*;
use std::cell::Cell;

// Go: project/dirty/box.go:3 Box
// PORT: Go `*Box` is shared and mutated, so the fields use `RefCell` and
// `Cell` and the methods take `&self`. `None` is the Go zero value (nil).
pub struct Box<T> {
    pub original: Option<T>,
    pub value: RefCell<Option<T>>,
    pub dirty: Cell<bool>,
    pub delete: Cell<bool>,
}

// Go: project/dirty/box.go:10 NewBox
pub fn new_box<T: Cloneable + Clone>(original: Option<T>) -> Rc<Box<T>> {
    Rc::new(Box {
        original: original.clone(),
        value: RefCell::new(original),
        dirty: Cell::new(false),
        delete: Cell::new(false),
    })
}

impl<T: Cloneable + Clone> Box<T> {
    // Go: project/dirty/box.go:14 Value
    pub fn value(&self) -> Option<T> {
        if self.delete.get() {
            return None;
        }
        self.value.borrow().clone()
    }

    // Go: project/dirty/box.go:22 Original
    pub fn original(&self) -> Option<T> {
        self.original.clone()
    }

    // Go: project/dirty/box.go:26 Dirty
    pub fn dirty(&self) -> bool {
        self.dirty.get()
    }

    // Go: project/dirty/box.go:30 Set
    pub fn set(&self, value: T) {
        *self.value.borrow_mut() = Some(value);
        self.delete.set(false);
        self.dirty.set(true);
    }

    // Go: project/dirty/box.go:36 Change
    pub fn change(&self, apply: &mut dyn FnMut(&T)) {
        if !self.dirty.get() {
            // PORT: Go calls Clone on a nil value; that dereferences nil.
            let value = self.value.borrow().clone();
            let cloned = value
                .as_ref()
                .expect("nil pointer dereference: Box.value")
                .clone_();
            *self.value.borrow_mut() = Some(cloned);
            self.dirty.set(true);
        }
        // PORT: no borrow is held while `apply` runs.
        let value = self.value.borrow().clone();
        apply(value.as_ref().expect("nil pointer dereference: Box.value"));
    }

    // Go: project/dirty/box.go:44 ChangeIf
    pub fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&T>) -> bool,
        apply: &mut dyn FnMut(&T),
    ) -> bool {
        let value = self.value.borrow().clone();
        if cond(value.as_ref()) {
            self.change(apply);
            return true;
        }
        false
    }

    // Go: project/dirty/box.go:52 Delete
    pub fn delete(&self) {
        self.delete.set(true);
    }

    // Go: project/dirty/box.go:56 Locked
    pub fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<T>)) {
        fn_(self);
    }

    // Go: project/dirty/box.go:60 Finalize
    pub fn finalize(&self) -> (Option<T>, bool) {
        (self.value(), self.dirty.get() || self.delete.get())
    }
}

impl<T: Cloneable + Clone> Value<T> for Box<T> {
    fn value(&self) -> Option<T> {
        Box::value(self)
    }

    fn original(&self) -> Option<T> {
        Box::original(self)
    }

    fn dirty(&self) -> bool {
        Box::dirty(self)
    }

    fn change(&self, apply: &mut dyn FnMut(&T)) {
        Box::change(self, apply)
    }

    fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&T>) -> bool,
        apply: &mut dyn FnMut(&T),
    ) -> bool {
        Box::change_if(self, cond, apply)
    }

    fn delete(&self) {
        Box::delete(self)
    }

    fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<T>)) {
        Box::locked(self, fn_)
    }
}
