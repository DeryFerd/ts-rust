//! Go `internal/project/dirty/interfaces.go`.
//!
//! Cross-unit decisions for `internal/project` and the packages that use it
//! (map-project.md section 4). Every project, ata, fs, collection, session
//! and ls/autoimport file follows them.
//!
//! 1. Threads. All project and language-service state lives on the one LSP
//!    dispatch thread (`Rc`, `RefCell`, `Cell`; not `Send`). Go
//!    `sync.Mutex`, `RWMutex` and `atomic.*` on that state become plain
//!    fields, `Cell` or `RefCell`. `collections.SyncMap` / `SyncSet` become
//!    `RefCell<FxHashMap>` / `RefCell<FxHashSet>` (`IndexMap` where Go
//!    iteration order reaches output). `core.WorkGroup`
//!    (`frontend::core_workgroup::new_work_group`, always the
//!    single-threaded group) and `core.BreadthFirstSearchParallelEx`
//!    (`frontend::core_bfs`) run serially in queue order. The BFS keeps
//!    Go's index checks, so it picks the in-order schedule. `go f()` over
//!    dispatch-thread state is `gostd::local::go`; timers are
//!    `gostd::local::after_func`.
//! 2. Pointers. A Go pointer to a shared struct (`*Project`,
//!    `*configFileEntry`, `*diskFile`, `*Snapshot`, ...) is `Rc<X>`, or
//!    `Rc<RefCell<X>>` when Go mutates it after sharing. A pointer that can
//!    be nil is `Option<..>`. Go pointer equality is `Rc::ptr_eq`
//!    (`std::ptr::eq` for `&'static compiler::NewProgram`). A pointer map
//!    key is `Rc::as_ptr(&p) as usize` (programs: `p as *const _ as usize`).
//! 3. `dirty` values. The value type `T` of `dirty::Box`, `dirty::Map` and
//!    `dirty::SyncMap` is the non-nil handle: `Rc<RefCell<X>>` for Go `*X`,
//!    `dirty::CloneableMap<K, V>` for a Go map. `T: Clone` copies the handle
//!    (a Go pointer copy), never the struct. `dirty::Cloneable::clone_` is Go
//!    `Clone()` (it makes a new handle). Where Go can hold or return the
//!    zero value (nil), the dirty API uses `Option<T>`: `value()` and
//!    `original()` return `Option<T>`, `change_if` and `delete_if` conditions
//!    get `Option<&T>`, finalization hooks get `Option<&V>`, and
//!    `dirty::new_box` takes `Option<T>`. `change(&mut |v: &T| ..)` gives the
//!    handle to `apply`, which mutates through `v.borrow_mut()` exactly as
//!    Go mutates through the pointer. Base maps are `FxHashMap<K, V>` (the
//!    PORTING default for a Go map). `Map` and `SyncMap` keep the base map
//!    in an `Rc`, because Go shares it: `new_map_shared` /
//!    `new_sync_map_shared` take it without a copy, and `finalize_shared`
//!    returns it unchanged when nothing changed, as Go does. `new_map` /
//!    `new_sync_map` take an owned map, and `finalize`, `finalize_exported`
//!    and `finalize_with` return an owned map (a copy when nothing changed).
//!    Constructors return `Rc` (Go returns pointers): `dirty::new_map`,
//!    `dirty::new_sync_map`, `dirty::new_box`, `dirty::new_map_builder`.
//!    Entries are `Rc<dirty::MapEntry<K, V>>` / `Rc<dirty::SyncMapEntry<K,
//!    V>>`. Go `dirty.Value[T]` is `&dyn dirty::Value<T>` or
//!    `Rc<dyn dirty::Value<T>>`, and a nil one is `None`. Go `(x, ok)`
//!    results stay tuples: `get`, `load` and `load_or_store` return
//!    `(Option<Rc<Entry>>, bool)`. Go `SyncMap.Finalize` is
//!    `finalize_exported` (Go also has an unexported `finalize`).
//! 4. Names. Other packages call these packages qualified, as Go does:
//!    `dirty::Box`, `dirty::Map`, `logging::LogTree`. Never glob
//!    `dirty::*` outside the dirty package: it would shadow std `Box`.
//!    Inside dirty files, std `Box` is `std::boxed::Box`.
//! 5. Loggers. Go `logging.Logger` is `Option<Rc<dyn logging::Logger>>`;
//!    `logging::new_nop_logger()` is `None` and `logging::new_logger(..)` is
//!    `Some(..)`. Go `*logging.LogTree` is `Option<Rc<logging::LogTree>>`;
//!    `logging::new_log_tree(..)` and `fork(..)` return it. Both `Option`
//!    types implement `logging::Logger`, and `Option<Rc<LogTree>>` also
//!    implements `logging::LogTreeMethods` (`embed`, `fork`, `string`), so a
//!    Go call on a maybe-nil logger keeps its shape: `logger.log(..)`,
//!    `logger.fork(..)`. Bring the two traits into scope to call them on the
//!    `Option`. Log arguments are preformatted (PORT: Go `...any` and
//!    `fmt.Sprint`): Go `Log(a, b)` is `log(&format!(..))` and `Logf(f, a)`
//!    is `logf(&format!(..))`.

use crate::project::dirty::prelude::*;

// Go: project/dirty/interfaces.go:3 Cloneable
// PORT: Go `Clone()`. The Rust name `clone_` keeps it apart from
// `std::clone::Clone::clone`, which copies the handle.
pub trait Cloneable {
    fn clone_(&self) -> Self;
}

// Go: project/dirty/interfaces.go:7 Value
// PORT: Go nil values are `None` (decision 3 above). `apply` gets the
// non-nil handle.
pub trait Value<T> {
    fn value(&self) -> Option<T>;
    fn original(&self) -> Option<T>;
    fn dirty(&self) -> bool;
    fn change(&self, apply: &mut dyn FnMut(&T));
    fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&T>) -> bool,
        apply: &mut dyn FnMut(&T),
    ) -> bool;
    fn delete(&self);
    fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<T>));
}
