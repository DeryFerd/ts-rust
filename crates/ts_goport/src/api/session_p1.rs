use crate::api::prelude::*;

// Port of Go `internal/api/session.go`, lines 1-1271: the snapshot
// registries, `Session`, `NewSession`, the checker and language service
// setup, the `HandleRequest` dispatch and the snapshot, project, symbol and
// type handlers up to `handleGetTargetOfSignature`, the transpile handlers
// (tsgo#4849), then `handleGetImportAdderEdits` and `toAPITextEdits`
// (tsgo#3881) and `originalTextOffset` (tsgo#4712). Lines 1272-2484 are
// `session_p2.rs`.
//
// PORT notes for both files:
// - Go `*ast.Symbol`, `*checker.Type` and `*checker.Signature` carry their
//   data. A Rust `SymbolId`, `TypeId` or `SignatureId` is an index into the
//   arenas of one checker, so a registry entry keeps the checker that made
//   the handle: `(Rc<RefCell<Checker>>, handle)`. Reads borrow that checker.
// - Handlers call a checker method in its own statement
//   (`setup.checker.borrow_mut().x(..)`), so no borrow is held when a
//   `new_*_response` borrows the checker again to read the result.
// - A handle from the registry is used with the setup checker only through
//   `checker_symbol`, `checker_type` and `checker_signature`. Go can hand a
//   pointer of one checker to another checker. For a symbol, the port uses
//   the same symbol when both arenas have it, else a shadow: a copy in the
//   setup checker's arena with the same id and no links (`import_symbol`).
//   A type or signature of another checker calls `unported!`.
// - Go `defer setup.done()`: `CheckerSetup::done` is a `Release` guard. It
//   releases the checker when `setup` drops at the end of the handler.
// - Current program: node handles (`node_handle_from`, `resolve_node_handle`)
//   and the source file encoder read lazy JSDoc through `prog()`. So every
//   handler that reads a program keeps it current for its whole body.
//   `setup_checker` does it through `done`. The handlers with no checker
//   call `ls_program::enter` after `get_program`. The `resolve*PropertyOf*`
//   helpers have no project, so they enter the program of the checker that
//   owns the handle.
// - Go mutexes (`snapshotsMu`, the registry mutexes) are dropped: the
//   session runs on the dispatch thread (PORTING "Threads").
// - The profile handlers run `crate::pprof`, which writes profiles with no
//   samples (see its module comment).

use crate::api::encoder;
use crate::astnav;
use crate::emitter::emitter::EmitOnly;
use crate::frontend::compiler;
use crate::frontend::core_context::{self, CheckerLifetime};
use crate::frontend::json_ext::{AnyValue, JsonValue};
use crate::frontend::tsoptions;
use crate::frontend::tspath;
use crate::frontend::vfs;
use crate::frontend::vfs::Fs as _;
use crate::gostd::{self, Context, GoError, errors};
use crate::ls;
use crate::ls::autoimport;
use crate::program::ls_program;
use crate::project;
use crate::transpile;
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

// Go: api/session.go:29 sessionIDCounter
pub static SESSION_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

// Go: api/session.go:31 snapshotData
// snapshotData holds the per-snapshot state including the snapshot itself
// and symbol/type registries scoped to this snapshot.
// Multiple clients may hold references to the same snapshot via ref counting;
// the registries are cleaned up when refCount reaches zero.
// PORT: registry values keep the checker that owns the handle (file header).
pub struct SnapshotData {
    pub snapshot: Rc<project::Snapshot>,
    pub ref_count: Cell<i32>,

    // Symbol IDs come from ast.GetSymbolId, a global atomic counter, so the same
    // *ast.Symbol pointer always has the same unique ID across all projects in the
    // snapshot. Symbols are registered snapshot-wide to ensure identity semantics:
    // querying the same symbol from two different projects returns the same handle.
    pub symbol_registry: RefCell<FxHashMap<SymbolID, (Rc<RefCell<Checker>>, SymbolId)>>,

    // symbolCanonicalProjects records, for each registered symbol, the project it was
    // first observed in. Because symbols are shared snapshot-wide (binder symbols are
    // attached to source files, which can be shared across projects), lookups that need
    // a project context (e.g. member/export ordering, node handle resolution) but don't
    // receive one from the caller default to this canonical project. First-writer wins so
    // the choice is stable. Guarded by symbolRegistryMu.
    pub symbol_canonical_projects: RefCell<FxHashMap<SymbolID, ProjectID>>,

    pub project_registries: RefCell<FxHashMap<ProjectID, Rc<ProjectRegistryData>>>,
}

// Go: api/session.go:64 projectRegistryData
// projectRegistryData holds per-project type and signature registries.
// Types and signatures use per-checker sequential IDs, so the same local ID
// can appear in multiple projects. Separate maps per project prevent collisions
// and allow clean teardown when a project is removed.
pub struct ProjectRegistryData {
    pub type_registry: RefCell<FxHashMap<TypeID, (Rc<RefCell<Checker>>, TypeId)>>,

    pub signature_registry: RefCell<FxHashMap<SignatureID, (Rc<RefCell<Checker>>, SignatureId)>>,
}

impl SnapshotData {
    // Go: api/session.go:49 getProgram
    // getProgram looks up a program from a project handle within this snapshot.
    pub fn get_program(
        &self,
        project_handle: &ProjectID,
    ) -> Result<Rc<compiler::NewProgram>, GoError> {
        let proj = self.get_project(project_handle)?;

        let program = proj.borrow().get_program();
        let Some(program) = program else {
            return Err(errors::errorf(
                format!("{}: project has no program", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        Ok(program)
    }

    // Go: api/session.go:88 getProject
    // getProject looks up a project from a project handle within this snapshot.
    pub fn get_project(
        &self,
        project_handle: &ProjectID,
    ) -> Result<Rc<RefCell<project::Project>>, GoError> {
        let project_name = parse_project_handle(project_handle);
        let proj = self
            .snapshot
            .project_collection
            .get_project_by_path(&project_name);
        let Some(proj) = proj else {
            return Err(errors::errorf(
                format!(
                    "{}: project {} not found",
                    *ERR_CLIENT_ERROR,
                    project_name.as_str()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        Ok(proj)
    }

    // Go: api/session.go:66 nodeHandleFrom
    // nodeHandleFrom creates an index-based node handle (index.kind.path), building a node index table
    // for the file on-demand if needed.
    pub fn node_handle_from(&self, node: Node) -> NodeHandle {
        let source_file = get_source_file_of_node(node);
        let path = source_file_info(source_file).path.clone();
        let table = encoder::get_node_index_table(source_file);
        let idx = table.get_index(node);
        NodeHandle(format!("{}.{}.{}", idx, node.kind() as i16, path))
    }

    // Go: api/session.go:108 getOrCreateProjectRegistry
    // getOrCreateProjectRegistry returns the registry for the given project, creating it if needed.
    pub fn get_or_create_project_registry(
        &self,
        project_id: &ProjectID,
    ) -> Rc<ProjectRegistryData> {
        if project_id.0.is_empty() {
            panic!("getOrCreateProjectRegistry: empty project ID");
        }
        self.project_registries
            .borrow_mut()
            .entry(project_id.clone())
            .or_insert_with(|| {
                Rc::new(ProjectRegistryData {
                    type_registry: RefCell::new(FxHashMap::default()),
                    signature_registry: RefCell::new(FxHashMap::default()),
                })
            })
            .clone()
    }

    // Go: api/session.go:135 newSymbolResponse
    // newSymbolResponse registers a symbol in the snapshot's registry and returns the response.
    // canonicalProject is the project the symbol was observed in and must be non-empty; it is recorded
    // as the symbol's canonical project (first writer wins) and returned to the client so it can default
    // project-scoped follow-up lookups (members/exports, node resolution) to it.
    // PORT: `checker` owns `symbol`; its arena holds the symbol data.
    pub fn new_symbol_response(
        &self,
        checker: &Rc<RefCell<Checker>>,
        symbol: SymbolId,
        canonical_project: &ProjectID,
    ) -> Option<SymbolResponse> {
        if symbol.is_nil() {
            return None;
        }

        let (id, project) = self.register_symbol(checker, symbol, canonical_project);
        let c = checker.borrow();
        let sym = c.sym(symbol);
        let mut resp = SymbolResponse {
            id,
            project,
            // PORT: Go `ast.EscapeSymbolName(symbol.Name)`. A private name
            // first gets the Go class id (`go_symbol_name`).
            name: escape_symbol_name(&go_symbol_name(&c.symbols, symbol)),
            flags: sym.flags.0,
            check_flags: sym.check_flags.0,
            ..Default::default()
        };

        if !sym.declarations.is_empty() {
            let mut declarations = Vec::with_capacity(sym.declarations.len());
            for &decl in sym.declarations.iter() {
                declarations.push(self.node_handle_from(decl));
            }
            resp.declarations = declarations;
        }

        if sym.value_declaration.is_some() {
            resp.value_declaration = self.node_handle_from(sym.value_declaration);
        }

        if sym.parent.is_some() {
            resp.parent = symbol_handle(&c.symbols, sym.parent);
        }

        if sym.export_symbol.is_some() {
            resp.export_symbol = symbol_handle(&c.symbols, sym.export_symbol);
        }

        Some(resp)
    }

    // Go: api/session.go:176 registerSymbol
    // registerSymbol registers a symbol in the snapshot's registry and returns its handle along with
    // its canonical project. The canonical project is the project the symbol was first observed in
    // (first writer wins for stability) and is always non-empty: every symbol handed to a client must
    // carry a project so that project-scoped follow-up lookups (members/exports, parent, node
    // resolution) have a default context. Callers must supply a non-empty project.
    pub fn register_symbol(
        &self,
        checker: &Rc<RefCell<Checker>>,
        symbol: SymbolId,
        canonical_project: &ProjectID,
    ) -> (SymbolID, ProjectID) {
        if symbol.is_nil() {
            return (SymbolID(0), ProjectID::default());
        }
        if canonical_project.0.is_empty() {
            panic!("registerSymbol requires a non-empty canonical project");
        }
        let (id, slot) = {
            let c = checker.borrow();
            (symbol_handle(&c.symbols, symbol), c.symbols.id_slot(symbol))
        };
        let mut registry = self.symbol_registry.borrow_mut();
        if let Some(existing) = registry.get(&id) {
            // PORT: Go compares `*ast.Symbol` pointers. The id slot stands
            // for the Go symbol (`SymbolArena::id_slot`): a binder symbol has
            // one slot in every checker that has it, and a shadow has the
            // slot of its origin (`import_symbol`).
            let same = existing.0.borrow().symbols.id_slot(existing.1) == slot;
            if !same {
                panic!("duplicate symbol");
            }
        } else {
            registry.insert(id, (checker.clone(), symbol));
        }
        let project = self
            .symbol_canonical_projects
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| canonical_project.clone())
            .clone();
        (id, project)
    }

    // Go: api/session.go:129 newTypeResponse
    // newTypeResponse registers a type in the project's registry and returns the response.
    pub fn new_type_response(
        &self,
        project_id: &ProjectID,
        checker: &Rc<RefCell<Checker>>,
        t: TypeId,
    ) -> Option<TypeResponse> {
        if t.is_nil() {
            return None;
        }
        let id = self.register_type(project_id, checker, t);
        Some(new_type_response(&checker.borrow(), t, id))
    }

    // Go: api/session.go:136 registerType
    pub fn register_type(
        &self,
        project_id: &ProjectID,
        checker: &Rc<RefCell<Checker>>,
        t: TypeId,
    ) -> TypeID {
        if t.is_nil() {
            return TypeID(0);
        }
        let id = type_handle(t);
        let reg = self.get_or_create_project_registry(project_id);
        let mut registry = reg.type_registry.borrow_mut();
        let existing = registry.get(&id);

        if let Some(existing) = existing {
            // PORT: Go compares `*checker.Type` pointers: same checker and
            // same arena index.
            if !(Rc::ptr_eq(&existing.0, checker) && existing.1 == t) {
                panic!("duplicate type");
            }
            return id;
        }
        registry.insert(id, (checker.clone(), t));
        id
    }

    // Go: api/session.go:157 resolveSymbolHandle
    // resolveSymbolHandle resolves a symbol handle within the snapshot's registry.
    // PORT: returns the checker that owns the symbol with it (file header).
    pub fn resolve_symbol_handle(
        &self,
        handle: SymbolID,
    ) -> Result<(Rc<RefCell<Checker>>, SymbolId), GoError> {
        if handle.0 == 0 {
            return Err(errors::errorf(
                format!("{}: empty symbol handle", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let symbol = self.symbol_registry.borrow().get(&handle).cloned();

        let Some(symbol) = symbol else {
            return Err(errors::errorf(
                format!(
                    "{}: symbol handle {} not found in snapshot registry",
                    *ERR_CLIENT_ERROR, handle.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        Ok(symbol)
    }

    // Go: api/session.go:174 resolveTypeHandle
    // resolveTypeHandle resolves a type handle within the project's registry.
    // PORT: returns the checker that owns the type with it (file header).
    pub fn resolve_type_handle(
        &self,
        project_id: &ProjectID,
        handle: TypeID,
    ) -> Result<(Rc<RefCell<Checker>>, TypeId), GoError> {
        if handle.0 == 0 {
            return Err(errors::errorf(
                format!("{}: empty type handle", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        if project_id.0.is_empty() {
            return Err(errors::errorf(
                format!(
                    "{}: empty project ID for type handle {}",
                    *ERR_CLIENT_ERROR, handle.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let reg = self.project_registries.borrow().get(project_id).cloned();

        let Some(reg) = reg else {
            return Err(errors::errorf(
                format!(
                    "{}: type handle {} not found (no registry for project {})",
                    *ERR_CLIENT_ERROR, handle.0, project_id.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        let t = reg.type_registry.borrow().get(&handle).cloned();

        let Some(t) = t else {
            return Err(errors::errorf(
                format!(
                    "{}: type handle {} not found in project registry",
                    *ERR_CLIENT_ERROR, handle.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        Ok(t)
    }

    // Go: api/session.go:191 resolveSignatureHandle
    // resolveSignatureHandle resolves a signature handle within the project's registry.
    // PORT: returns the checker that owns the signature with it (file header).
    pub fn resolve_signature_handle(
        &self,
        project_id: &ProjectID,
        handle: SignatureID,
    ) -> Result<(Rc<RefCell<Checker>>, SignatureId), GoError> {
        if handle.0 == 0 {
            return Err(errors::errorf(
                format!("{}: empty signature handle", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        if project_id.0.is_empty() {
            return Err(errors::errorf(
                format!(
                    "{}: empty project ID for signature handle {}",
                    *ERR_CLIENT_ERROR, handle.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let reg = self.project_registries.borrow().get(project_id).cloned();

        let Some(reg) = reg else {
            return Err(errors::errorf(
                format!(
                    "{}: signature handle {} not found (no registry for project {})",
                    *ERR_CLIENT_ERROR, handle.0, project_id.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        let sig = reg.signature_registry.borrow().get(&handle).cloned();

        let Some(sig) = sig else {
            return Err(errors::errorf(
                format!(
                    "{}: signature handle {} not found in project registry",
                    *ERR_CLIENT_ERROR, handle.0
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        Ok(sig)
    }

    // Go: api/session.go:208 newSignatureResponse
    // newSignatureResponse registers a signature in the project's registry and returns the response.
    pub fn new_signature_response(
        &self,
        project_id: &ProjectID,
        checker: &Rc<RefCell<Checker>>,
        sig: SignatureId,
    ) -> Option<SignatureResponse> {
        if sig.is_nil() {
            return None;
        }
        let c = checker.borrow();
        let s = c.sig(sig);
        let mut resp = SignatureResponse {
            id: self.register_signature(project_id, checker, sig),
            flags: s.flags().0,
            ..Default::default()
        };

        if s.declaration().is_some() {
            resp.declaration = self.node_handle_from(s.declaration());
        }

        if !s.type_parameters().is_empty() {
            resp.type_parameters = type_handles(s.type_parameters());
        }

        if !s.parameters().is_empty() {
            resp.parameters = symbol_handles(&c.symbols, s.parameters());
        }

        if s.this_parameter().is_some() {
            resp.this_parameter = symbol_handle(&c.symbols, s.this_parameter());
        }

        if s.target().is_some() {
            resp.target = signature_handle(s.target());
        }

        Some(resp)
    }

    // Go: api/session.go:240 registerSignature
    pub fn register_signature(
        &self,
        project_id: &ProjectID,
        checker: &Rc<RefCell<Checker>>,
        sig: SignatureId,
    ) -> SignatureID {
        if sig.is_nil() {
            return SignatureID(0);
        }
        let id = signature_handle(sig);
        let reg = self.get_or_create_project_registry(project_id);
        let mut registry = reg.signature_registry.borrow_mut();
        let existing = registry.get(&id);

        if let Some(existing) = existing {
            // PORT: Go compares `*checker.Signature` pointers: same checker
            // and same arena index.
            if !(Rc::ptr_eq(&existing.0, checker) && existing.1 == sig) {
                panic!("duplicate signature");
            }
            return id;
        }
        registry.insert(id, (checker.clone(), sig));
        id
    }
}

/// PORT: Go hands a `*ast.Symbol` of any checker to `setup.checker`. A Rust
/// symbol handle indexes the arena of `owner`. This returns the symbol of
/// `checker`'s arena that is the same Go symbol (`import_symbol`).
pub fn checker_symbol(
    checker: &Rc<RefCell<Checker>>,
    owner: &Rc<RefCell<Checker>>,
    symbol: SymbolId,
) -> SymbolId {
    if Rc::ptr_eq(checker, owner) || symbol.is_nil() {
        return symbol;
    }
    let owner = owner.borrow();
    let mut checker = checker.borrow_mut();
    import_symbol(&owner.symbols, &mut checker.symbols, symbol)
}

/// The symbol of arena `to` that is Go symbol `symbol` of arena `from`: the
/// same symbol when `to` has it, else a shadow in `to`
/// (`SymbolArena::push_shadow`): a copy with the same id. The checker of
/// `to` has no links for a shadow, as a Go checker has none for the symbol
/// of another checker, so it computes the type from the declarations or
/// dereferences nil (an instantiated symbol has no target). The symbol and
/// table fields of a shadow point into `to` in the same way. Nodes and
/// names are global and stay.
// PORT: Go shares the object, so a later write to its fields is seen by
// both checkers. Checkers write those fields almost only while they make or
// merge the symbol. A work list, not recursion: parents and members form
// cycles and long chains.
fn import_symbol(from: &SymbolArena, to: &mut SymbolArena, symbol: SymbolId) -> SymbolId {
    let mut work = Vec::new();
    let result = shadow_of(from, to, symbol, &mut work);
    while let Some((shadow, origin)) = work.pop() {
        let s = from.sym(origin);
        let (parent, export_symbol, members, exports) =
            (s.parent, s.export_symbol, s.members, s.exports);
        let parent = shadow_of(from, to, parent, &mut work);
        let export_symbol = shadow_of(from, to, export_symbol, &mut work);
        let members = import_table(from, to, members, &mut work);
        let exports = import_table(from, to, exports, &mut work);
        let s = to.sym_mut(shadow);
        s.parent = parent;
        s.export_symbol = export_symbol;
        s.members = members;
        s.exports = exports;
    }
    result
}

/// `symbol` of `from` in `to`: the same symbol, or its shadow. A new shadow
/// still holds the symbol and table fields of `from`, so it goes on `work`
/// with its origin, and `import_symbol` maps them.
fn shadow_of(
    from: &SymbolArena,
    to: &mut SymbolArena,
    symbol: SymbolId,
    work: &mut Vec<(SymbolId, SymbolId)>,
) -> SymbolId {
    if symbol.is_nil() {
        return symbol;
    }
    let origin = from.id_slot(symbol);
    if let Some(found) = to.symbol_at_slot(origin) {
        return found;
    }
    let shadow = to.push_shadow(from.sym(symbol).clone(), origin);
    work.push((shadow, symbol));
    shadow
}

/// `table` of `from` in `to`: the same table when both arenas copied it from
/// the binder lineage, else a new table in `to` with the same entries in the
/// same order, each symbol in `to` (`shadow_of`).
fn import_table(
    from: &SymbolArena,
    to: &mut SymbolArena,
    table: SymbolTable,
    work: &mut Vec<(SymbolId, SymbolId)>,
) -> SymbolTable {
    if table.is_nil() || table.index() < from.shared_table_count().min(to.shared_table_count()) {
        return table;
    }
    let entries: Vec<_> = from
        .iter_names(table)
        .map(|(name, symbol)| (name, shadow_of(from, to, symbol, work)))
        .collect();
    to.push_table_from_entries(entries.into_iter())
}

/// PORT: as `checker_symbol`, for a type. Every type belongs to one checker.
/// Go can mix types of two checkers (a canceled persistent checker, a second
/// project); the port can not. A copy, as for a symbol, does not give Go's
/// answers: Go's checkers write lazy results (resolved members, return
/// types) into the shared type and read each other's results, and they
/// number types each from 1, so ids collide (`duplicate type`). Only one
/// object heap for all checkers would match that.
pub fn checker_type(
    checker: &Rc<RefCell<Checker>>,
    owner: &Rc<RefCell<Checker>>,
    t: TypeId,
) -> TypeId {
    if !Rc::ptr_eq(checker, owner) {
        unported!("api: type of another checker");
    }
    t
}

/// PORT: as `checker_type`, for a signature, for the same reason.
pub fn checker_signature(
    checker: &Rc<RefCell<Checker>>,
    owner: &Rc<RefCell<Checker>>,
    sig: SignatureId,
) -> SignatureId {
    if !Rc::ptr_eq(checker, owner) {
        unported!("api: signature of another checker");
    }
    sig
}

// Go: api/session.go:265 Session
// Session represents an API session that provides programmatic access
// to TypeScript language services through the LSP server.
// It implements the Handler interface to process incoming API requests.
// The session supports multiple active snapshots, each with their own
// symbol and type registries for maintaining object identity.
pub struct Session {
    pub id: String,
    pub project_session: Rc<project::Session>,

    // This is set to true when using MessagePackProtocol.
    pub use_binary_responses: bool,

    // snapshots maps snapshot handles to their data. Each snapshot has its own
    // symbol/type registries.
    // PORT: the port is one thread, so the Go `snapshotsMu` and `updateMu`
    // locks are not ported.
    pub snapshots: RefCell<FxHashMap<SnapshotID, Rc<SnapshotData>>>,

    // latestSnapshot tracks the most recently created snapshot, used as the diff base
    // for the next update.
    pub latest_snapshot: Cell<SnapshotID>,

    // openProjects and openFiles track the projects and files this session
    // currently holds open in the project session's API state. The session holds
    // at most one ref per project/file (opens are idempotent), so it can release
    // exactly those refs on Close and never send a close for a ref it doesn't hold.
    pub open_projects: RefCell<FxHashSet<tspath::Path>>,
    pub open_files: RefCell<FxHashSet<tspath::Path>>,

    pub cpu_profiler: crate::pprof::CpuProfiler,
}

// Go: api/session.go:284 `var _ Handler = (*Session)(nil)`
// Ensure Session implements Handler
// PORT: the `impl Handler for Session` below.

// Go: api/session.go:287 SessionOptions
// SessionOptions configures an API session.
#[derive(Clone, Debug, Default)]
pub struct SessionOptions {
    // UseBinaryResponses enables binary responses for msgpack protocol.
    pub use_binary_responses: bool,
}

// Go: api/session.go:293 NewSession
// NewSession creates a new API session with the given project session.
pub fn new_session(
    project_session: Rc<project::Session>,
    options: Option<&SessionOptions>,
) -> Rc<Session> {
    let id = SESSION_ID_COUNTER.fetch_add(1, Ordering::SeqCst) + 1;
    let mut s = Session {
        id: format_session_id(id),
        project_session,
        use_binary_responses: false,
        snapshots: RefCell::new(FxHashMap::default()),
        latest_snapshot: Cell::new(SnapshotID(0)),
        open_projects: RefCell::new(FxHashSet::default()),
        open_files: RefCell::new(FxHashSet::default()),
        cpu_profiler: crate::pprof::CpuProfiler::default(),
    };
    if let Some(options) = options {
        s.use_binary_responses = options.use_binary_responses;
    }
    Rc::new(s)
}

// PORT: Go `project.Session` satisfies `tsoptions.ParseConfigHost` through
// its `FS` and `GetCurrentDirectory` methods (handleParseConfigFile passes
// it). Rust needs the impl; it forwards to the inherent methods.
impl tsoptions::ParseConfigHost for project::Session {
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        project::Session::fs(self)
    }

    fn get_current_directory(&self) -> String {
        project::Session::get_current_directory(self)
    }
}

// Go: api/session.go:317 snapshotHandle
// snapshotHandle creates a snapshot handle from a snapshot's ID.
pub fn snapshot_handle(snapshot: &project::Snapshot) -> SnapshotID {
    SnapshotID(snapshot.id())
}

// Go: api/session.go:333 checkerSetup
// checkerSetup holds the common context needed by handlers that require a type checker.
// PORT: Go `done func()` is the `Release` guard; it runs when the setup drops.
pub struct CheckerSetup {
    pub sd: Rc<SnapshotData>,
    pub program: Rc<compiler::NewProgram>,
    pub checker: Rc<RefCell<Checker>>,
    pub done: ls_program::Release,
    pub project_id: ProjectID,
}

impl CheckerSetup {
    // Go: api/session.go:464 checkerSetup.newTypeResponse
    pub fn new_type_response(&self, t: TypeId) -> Option<TypeResponse> {
        self.sd
            .new_type_response(&self.project_id, &self.checker, t)
    }

    // Go: api/session.go:468 checkerSetup.newSymbolResponse
    pub fn new_symbol_response(&self, sym: SymbolId) -> Option<SymbolResponse> {
        self.sd
            .new_symbol_response(&self.checker, sym, &self.project_id)
    }

    // Go: api/session.go:472 checkerSetup.newSignatureResponse
    pub fn new_signature_response(&self, sig: SignatureId) -> Option<SignatureResponse> {
        self.sd
            .new_signature_response(&self.project_id, &self.checker, sig)
    }

    // Go: api/session.go:476 checkerSetup.resolveTypeHandle
    pub fn resolve_type_handle(
        &self,
        id: TypeID,
    ) -> Result<(Rc<RefCell<Checker>>, TypeId), GoError> {
        self.sd.resolve_type_handle(&self.project_id, id)
    }

    // Go: api/session.go:480 checkerSetup.resolveSymbolHandle
    pub fn resolve_symbol_handle(
        &self,
        id: SymbolID,
    ) -> Result<(Rc<RefCell<Checker>>, SymbolId), GoError> {
        self.sd.resolve_symbol_handle(id)
    }

    // Go: api/session.go:484 checkerSetup.resolveSignatureHandle
    pub fn resolve_signature_handle(
        &self,
        id: SignatureID,
    ) -> Result<(Rc<RefCell<Checker>>, SignatureId), GoError> {
        self.sd.resolve_signature_handle(&self.project_id, id)
    }

    // Go: api/session.go:525 checkerSetup.resolveLocation
    // resolveLocation resolves an optional location, given either as a node handle or as a
    // file and position. Returns nil when neither is provided.
    pub fn resolve_location(
        &self,
        handle: &NodeHandle,
        file: Option<&DocumentIdentifier>,
        position: Option<u32>,
    ) -> Result<Node, GoError> {
        if !handle.0.is_empty() {
            return self.sd.resolve_node_handle(&self.program, handle);
        }
        if let (Some(file), Some(position)) = (file, position) {
            let source_file = self
                .program
                .get_source_file(&file.to_file_name())
                .map_or(Node::NIL, |f| f.root);
            if source_file.is_nil() {
                return Err(errors::errorf(
                    format!(
                        "{}: source file not found: {}",
                        *ERR_CLIENT_ERROR,
                        file.string()
                    ),
                    vec![ERR_CLIENT_ERROR.clone()],
                ));
            }
            return Ok(astnav::get_touching_property_name(
                source_file,
                source_file_get_position_map(source_file).utf16_to_utf8(position as i32),
            ));
        }
        Ok(Node::NIL)
    }
}

/// PORT: Go returns a typed handler result as `any`. A typed nil pointer or
/// slice is still a non-nil `any` (it marshals as `null` or `[]`), so every
/// typed result is `Some`.
pub fn to_any<T: AnyValue>(v: T) -> Option<Box<dyn AnyValue>> {
    Some(Box::new(v))
}

/// PORT: Go `parsed.(*T)`. `unmarshallerFor[T]` always returns a `*T`, so the
/// assertion holds; a failed one panics as in Go.
fn assert_params<T: 'static>(parsed: &Option<Box<dyn AnyValue>>) -> &T {
    match parsed.as_deref().and_then(|p| p.downcast_ref::<T>()) {
        Some(p) => p,
        None => panic!(
            "interface conversion: interface {{}} is not *{}",
            std::any::type_name::<T>()
        ),
    }
}

impl Session {
    // Go: api/session.go:307 ID
    // ID returns the unique identifier for this session.
    pub fn id(&self) -> String {
        self.id.clone()
    }

    // Go: api/session.go:312 ProjectSession
    // ProjectSession returns the underlying project session.
    pub fn project_session(&self) -> Rc<project::Session> {
        self.project_session.clone()
    }

    // Go: api/session.go:322 getSnapshotData
    // getSnapshotData looks up snapshot data by handle.
    pub fn get_snapshot_data(&self, handle: SnapshotID) -> Result<Rc<SnapshotData>, GoError> {
        let sd = self.snapshots.borrow().get(&handle).cloned();
        let Some(sd) = sd else {
            return Err(errors::errorf(
                format!("{}: snapshot {} not found", *ERR_CLIENT_ERROR, handle.0),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        Ok(sd)
    }

    // Go: api/session.go:463 retainSnapshotData (tsgo#4642)
    // retainSnapshotData pins snapshot data while an operation builds a derived snapshot.
    pub fn retain_snapshot_data(&self, handle: SnapshotID) -> Result<Rc<SnapshotData>, GoError> {
        let sd = self.snapshots.borrow().get(&handle).cloned();
        let Some(sd) = sd else {
            return Err(errors::errorf(
                format!("{}: snapshot {} not found", *ERR_CLIENT_ERROR, handle.0),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        sd.ref_count.set(sd.ref_count.get() + 1);
        Ok(sd)
    }

    // Go: api/session.go:474 releaseSnapshot (tsgo#4642)
    pub fn release_snapshot(&self, handle: SnapshotID) -> Result<(), GoError> {
        let sd = self.snapshots.borrow().get(&handle).cloned();
        let Some(sd) = sd else {
            return Err(errors::errorf(
                format!("{}: snapshot {} not found", *ERR_CLIENT_ERROR, handle.0),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        sd.ref_count.set(sd.ref_count.get() - 1);
        if sd.ref_count.get() <= 0 {
            self.snapshots.borrow_mut().remove(&handle);
            project::Snapshot::deref(&sd.snapshot, &self.project_session);
        }
        Ok(())
    }

    // Go: api/session.go:342 setupChecker
    // setupChecker resolves snapshot, program, and type checker for a project.
    // Callers must defer setup.done() to release the checker.
    pub fn setup_checker(
        &self,
        ctx: &Context,
        snapshot: SnapshotID,
        project_handle: &ProjectID,
    ) -> Result<CheckerSetup, GoError> {
        let sd = self.get_snapshot_data(snapshot)?;

        let program = sd.get_program(project_handle)?;

        let (c, done) = ls_program::get_type_checker(
            &program,
            &core_context::with_checker_lifetime(ctx, CheckerLifetime::API),
        );
        Ok(CheckerSetup {
            sd,
            program,
            checker: c,
            done,
            project_id: project_handle.clone(),
        })
    }

    // Go: api/session.go:365 setupLanguageService
    // setupLanguageService creates a LanguageService for the given snapshot/project.
    // Unlike setupChecker, this does NOT acquire a checker from the pool, so callers that
    // only need an LS (and not a Checker) can avoid blocking on / holding a pooled checker.
    //
    // The LS acquires its own checker internally (keyed by the ctx's checker lifetime).
    // If a handler returns symbol/type/signature handles the client may later re-query
    // on the API checker (e.g. completion with IncludeSymbol -> GetTypeOfSymbol), wrap
    // ctx with core.WithCheckerLifetime(ctx, core.CheckerLifetimeAPI) so those handles
    // are produced on the persistent API checker and stay resolvable. Only safe when the
    // LS operation acquires a checker exactly once; nested acquisitions (e.g. find-all-
    // references) would deadlock on the single-slot persistent checker.
    pub fn setup_language_service(
        &self,
        sd: &SnapshotData,
        program: Rc<compiler::NewProgram>,
        project_handle: &ProjectID,
        active_file: &str,
    ) -> Result<ls::LanguageService, GoError> {
        let project_name = parse_project_handle(project_handle);
        let proj = sd
            .snapshot
            .project_collection
            .get_project_by_path(&project_name);
        let Some(proj) = proj else {
            return Err(errors::errorf(
                format!(
                    "{}: project {} not found",
                    *ERR_CLIENT_ERROR,
                    project_name.as_str()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        let project_id = proj.borrow().id();
        let host: Rc<dyn ls::Host> = sd.snapshot.clone();
        Ok(ls::new_language_service(
            project_id,
            program,
            host,
            active_file,
        ))
    }
}

impl ipc::Handler for Session {
    // Go: api/session.go:375 HandleRequest
    // HandleRequest implements Handler.
    fn handle_request(
        &self,
        ctx: &Context,
        method: &str,
        params: JsonValue,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        // Handle simple methods that don't need param parsing
        match method {
            "echo" => {
                // Return raw binary for msgpack protocol compatibility
                if self.use_binary_responses {
                    return Ok(to_any(RawBinary(params.0)));
                }
                return Ok(to_any(params));
            }
            "ping" => {
                return Ok(to_any("pong".to_string()));
            }
            _ => {}
        }

        let parsed = match unmarshal_payload(method, &params) {
            Ok(parsed) => parsed,
            Err(err) => {
                return Err(errors::errorf(
                    format!("{}: {}", *ERR_INVALID_REQUEST, err),
                    vec![ERR_INVALID_REQUEST.clone(), err],
                ));
            }
        };

        match method {
            // ts#63937
            m if m == Method::BATCH_REQUESTS.0 => self
                .handle_batch_requests(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::RELEASE.0 => self.handle_release(ctx, Some(assert_params(&parsed))),
            m if m == Method::INITIALIZE.0 => self.handle_initialize(ctx).map(to_any),
            m if m == Method::UPDATE_SNAPSHOT.0 => self
                .handle_update_snapshot(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::UPDATE_TEMPORARY_SNAPSHOT.0 => self
                .handle_update_temporary_snapshot(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::PARSE_COMMAND_LINE.0 => self
                .handle_parse_command_line(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::READ_CONFIG_FILE.0 => self
                .handle_read_config_file(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::PARSE_JSON_CONFIG_FILE.0 => self
                .handle_parse_json_config_file_content(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::PARSE_CONFIG_FILE.0 => self
                .handle_parse_config_file(ctx, assert_params(&parsed))
                .map(to_any),
            // tsgo#4849
            m if m == Method::TRANSPILE_MODULE.0 => self
                .handle_transpile(ctx, assert_params(&parsed), false)
                .map(to_any),
            m if m == Method::TRANSPILE_MODULE_FROM_FILE.0 => self
                .handle_transpile_from_file(ctx, assert_params(&parsed), false)
                .map(to_any),
            m if m == Method::TRANSPILE_DECLARATION.0 => self
                .handle_transpile(ctx, assert_params(&parsed), true)
                .map(to_any),
            m if m == Method::TRANSPILE_DECLARATION_FROM_FILE.0 => self
                .handle_transpile_from_file(ctx, assert_params(&parsed), true)
                .map(to_any),
            m if m == Method::GET_DEFAULT_PROJECT_FOR_FILE.0 => self
                .handle_get_default_project_for_file(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SOURCE_FILE.0 => {
                self.handle_get_source_file(ctx, assert_params(&parsed))
            }
            m if m == Method::GET_SOURCE_FILE_NAMES.0 => self
                .handle_get_source_file_names(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SOURCE_FILE_METADATA.0 => self
                .handle_get_source_file_metadata(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONFIG_FILE_NAMES.0 => self
                .handle_get_config_file_names(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONFIG_SOURCE_FILE.0 => {
                self.handle_get_config_source_file(ctx, assert_params(&parsed))
            }
            m if m == Method::GET_SYMBOL_AT_POSITION.0 => self
                .handle_get_symbol_at_position(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOLS_AT_POSITIONS.0 => self
                .handle_get_symbols_at_positions(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOL_AT_LOCATION.0 => self
                .handle_get_symbol_at_location(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOLS_AT_LOCATIONS.0 => self
                .handle_get_symbols_at_locations(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOL_OF_SOURCE_FILE.0 => self
                .handle_get_symbol_of_source_file(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOLS_OF_SOURCE_FILES.0 => self
                .handle_get_symbols_of_source_files(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_OF_SYMBOL.0 => self
                .handle_get_type_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPES_OF_SYMBOLS.0 => self
                .handle_get_types_of_symbols(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_DECLARED_TYPE_OF_SYMBOL.0 => self
                .handle_get_declared_type_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::RESOLVE_NAME.0 => self
                .handle_resolve_name(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOLS_IN_SCOPE.0 => self
                .handle_get_symbols_in_scope(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SIGNATURES_OF_TYPE.0 => self
                .handle_get_signatures_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_RESOLVED_SIGNATURE.0 => self
                .handle_get_resolved_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_AT_LOCATION.0 => self
                .handle_get_type_at_location(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_AT_LOCATIONS.0 => self
                .handle_get_type_at_locations(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_AT_POSITION.0 => self
                .handle_get_type_at_position(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPES_AT_POSITIONS.0 => self
                .handle_get_types_at_positions(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PARENT_OF_SYMBOL.0 => self
                .handle_get_parent_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_MEMBERS_OF_SYMBOL.0 => self
                .handle_get_members_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_EXPORTS_OF_SYMBOL.0 => self
                .handle_get_exports_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_EXPORT_SYMBOL_OF_SYMBOL.0 => self
                .handle_get_export_symbol_of_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYMBOL_OF_TYPE.0 => self
                .handle_get_symbol_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TARGET_OF_TYPE.0 => self
                .handle_get_target_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_FRESH_TYPE_OF_TYPE.0 => self
                .handle_get_fresh_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_REGULAR_TYPE_OF_TYPE.0 => self
                .handle_get_regular_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPES_OF_TYPE.0 => self
                .handle_get_types_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_PARAMETERS_OF_TYPE.0 => self
                .handle_get_type_parameters_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_OUTER_TYPE_PARAMETERS_OF_TYPE.0 => self
                .handle_get_outer_type_parameters_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_LOCAL_TYPE_PARAMETERS_OF_TYPE.0 => self
                .handle_get_local_type_parameters_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_ALIAS_TYPE_ARGUMENTS_OF_TYPE.0 => self
                .handle_get_alias_type_arguments_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_ALIAS_SYMBOL_OF_TYPE.0 => self
                .handle_get_alias_symbol_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_OBJECT_TYPE_OF_TYPE.0 => self
                .handle_get_object_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_INDEX_TYPE_OF_TYPE.0 => self
                .handle_get_index_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CHECK_TYPE_OF_TYPE.0 => self
                .handle_get_check_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_EXTENDS_TYPE_OF_TYPE.0 => self
                .handle_get_extends_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_BASE_TYPE_OF_TYPE.0 => self
                .handle_get_base_type_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONSTRAINT_OF_TYPE.0 => self
                .handle_get_constraint_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TRUE_TYPE_OF_CONDITIONAL_TYPE.0 => self
                .handle_get_true_type_of_conditional_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_FALSE_TYPE_OF_CONDITIONAL_TYPE.0 => self
                .handle_get_false_type_of_conditional_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_PARAMETERS_OF_SIGNATURE.0 => self
                .handle_get_type_parameters_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PARAMETERS_OF_SIGNATURE.0 => self
                .handle_get_parameters_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_THIS_PARAMETER_OF_SIGNATURE.0 => self
                .handle_get_this_parameter_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TARGET_OF_SIGNATURE.0 => self
                .handle_get_target_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONTEXTUAL_TYPE.0 => self
                .handle_get_contextual_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_BASE_TYPE_OF_LITERAL_TYPE.0 => self
                .handle_get_base_type_of_literal_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_NON_NULLABLE_TYPE.0 => self
                .handle_get_non_nullable_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_FROM_TYPE_NODE.0 => self
                .handle_get_type_from_type_node(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_WIDENED_TYPE.0 => self
                .handle_get_widened_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PARAMETER_TYPE.0 => self
                .handle_get_parameter_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_PARAMETER_AT_POSITION.0 => self
                .handle_get_type_parameter_at_position(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::IS_ARRAY_LIKE_TYPE.0 => self
                .handle_is_array_like_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::IS_TYPE_ASSIGNABLE_TO.0 => self
                .handle_is_type_assignable_to(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SHORTHAND_ASSIGNMENT_VALUE_SYMBOL.0 => self
                .handle_get_shorthand_assignment_value_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_OF_SYMBOL_AT_LOCATION.0 => self
                .handle_get_type_of_symbol_at_location(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::TYPE_TO_TYPE_NODE.0 => {
                self.handle_type_to_type_node(ctx, assert_params(&parsed))
            }
            m if m == Method::SIGNATURE_TO_SIGNATURE_DECLARATION.0 => {
                self.handle_signature_to_signature_declaration(ctx, assert_params(&parsed))
            }
            m if m == Method::TYPE_TO_STRING.0 => {
                self.handle_type_to_string(ctx, assert_params(&parsed))
            }
            m if m == Method::PRINT_NODE.0 => self
                .handle_print_node(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::FORMAT_NODE_FOR_INSERTION.0 => self
                .handle_format_node_for_insertion(ctx, assert_params(&parsed))
                .map(to_any),
            // tsgo#4699
            m if m == Method::EMIT.0 => self.handle_emit(ctx, assert_params(&parsed)).map(to_any),
            m if m == Method::EMIT_TO_STRING.0 => self
                .handle_emit_to_string(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_JAVA_SCRIPT_EMIT.0 => self
                .handle_selected_files_emit(ctx, assert_params(&parsed), EmitOnly::Js)
                .map(to_any),
            m if m == Method::GET_DECLARATION_EMIT.0 => self
                .handle_selected_files_emit(ctx, assert_params(&parsed), EmitOnly::Dts)
                .map(to_any),
            m if m == Method::IS_CONTEXT_SENSITIVE.0 => self
                .handle_is_context_sensitive(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_RETURN_TYPE_OF_SIGNATURE.0 => self
                .handle_get_return_type_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_REST_TYPE_OF_SIGNATURE.0 => self
                .handle_get_rest_type_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_PREDICATE_OF_SIGNATURE.0 => self
                .handle_get_type_predicate_of_signature(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_BASE_TYPES.0 => self
                .handle_get_base_types(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PROPERTIES_OF_TYPE.0 => self
                .handle_get_properties_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_APPARENT_PROPERTIES_OF_TYPE.0 => self
                .handle_get_apparent_properties_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_APPARENT_TYPE.0 => self
                .handle_get_apparent_type(ctx, assert_params(&parsed))
                .map(to_any),
            // ts#63899
            m if m == Method::GET_REDUCED_TYPE.0 => self
                .handle_get_reduced_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PROPERTY_OF_TYPE.0 => self
                .handle_get_property_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_INDEX_INFOS_OF_TYPE.0 => self
                .handle_get_index_infos_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONSTRAINT_OF_TYPE_PARAMETER.0 => self
                .handle_get_constraint_of_type_parameter(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_BASE_CONSTRAINT_OF_TYPE.0 => self
                .handle_get_base_constraint_of_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_DEFAULT_FROM_TYPE_PARAMETER.0 => self
                .handle_get_default_from_type_parameter(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_TYPE_ARGUMENTS.0 => self
                .handle_get_type_arguments(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_IMPORT_ADDER_EDITS.0 => self
                .handle_get_import_adder_edits(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONSTANT_VALUE.0 => {
                self.handle_get_constant_value(ctx, assert_params(&parsed))
            }
            m if m == Method::GET_SIGNATURE_FROM_DECLARATION.0 => self
                .handle_get_signature_from_declaration(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_EXPORT_SPECIFIER_LOCAL_TARGET.0 => self
                .handle_get_export_specifier_local_target_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_ALIASED_SYMBOL.0 => self
                .handle_get_aliased_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_IMMEDIATE_ALIASED_SYMBOL.0 => self
                .handle_get_immediate_aliased_symbol(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_FULLY_QUALIFIED_NAME.0 => self
                .handle_get_fully_qualified_name(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_EXPORTS_OF_MODULE.0 => self
                .handle_get_exports_of_module(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_MEMBER_IN_MODULE_EXPORTS.0 => self
                .handle_get_member_in_module_exports(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_JS_DOC_TAGS.0 => self
                .handle_get_js_doc_tags(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_DOCUMENTATION_COMMENT.0 => self
                .handle_get_documentation_comment(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::IS_ARRAY_TYPE.0 => self
                .handle_is_array_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::IS_TUPLE_TYPE.0 => self
                .handle_is_tuple_type(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_ANY_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_any_type)
                .map(to_any),
            m if m == Method::GET_STRING_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_string_type)
                .map(to_any),
            m if m == Method::GET_NUMBER_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_number_type)
                .map(to_any),
            m if m == Method::GET_BOOLEAN_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_boolean_type)
                .map(to_any),
            m if m == Method::GET_VOID_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_void_type)
                .map(to_any),
            m if m == Method::GET_UNDEFINED_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_undefined_type)
                .map(to_any),
            m if m == Method::GET_NULL_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_null_type)
                .map(to_any),
            m if m == Method::GET_NEVER_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_never_type)
                .map(to_any),
            m if m == Method::GET_UNKNOWN_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_unknown_type)
                .map(to_any),
            m if m == Method::GET_BIG_INT_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_big_int_type)
                .map(to_any),
            m if m == Method::GET_ES_SYMBOL_TYPE.0 => self
                .handle_get_intrinsic_type(ctx, assert_params(&parsed), Checker::get_es_symbol_type)
                .map(to_any),
            m if m == Method::GET_NON_PRIMITIVE_TYPE.0 => self
                .handle_get_intrinsic_type(
                    ctx,
                    assert_params(&parsed),
                    Checker::get_non_primitive_type,
                )
                .map(to_any),
            m if m == Method::GET_WELL_KNOWN_SYMBOLS.0 => self
                .handle_get_well_known_symbols(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_WELL_KNOWN_SIGNATURES.0 => self
                .handle_get_well_known_signatures(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SYNTACTIC_DIAGNOSTICS.0 => self
                .handle_get_syntactic_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_BIND_DIAGNOSTICS.0 => self
                .handle_get_bind_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SEMANTIC_DIAGNOSTICS.0 => self
                .handle_get_semantic_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SUGGESTION_DIAGNOSTICS.0 => self
                .handle_get_suggestion_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_DECLARATION_DIAGNOSTICS.0 => self
                .handle_get_declaration_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_PROGRAM_DIAGNOSTICS.0 => self
                .handle_get_program_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_GLOBAL_DIAGNOSTICS.0 => self
                .handle_get_global_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_CONFIG_FILE_PARSING_DIAGNOSTICS.0 => self
                .handle_get_config_file_parsing_diagnostics(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::START_CPU_PROFILE.0 => {
                self.handle_start_cpu_profile(ctx, Some(assert_params(&parsed)))
            }
            m if m == Method::STOP_CPU_PROFILE.0 => self.handle_stop_cpu_profile(ctx).map(to_any),
            m if m == Method::SAVE_HEAP_PROFILE.0 => self
                .handle_save_heap_profile(ctx, Some(assert_params(&parsed)))
                .map(to_any),
            m if m == Method::GET_REFERENCES_TO_SYMBOL_IN_FILE.0 => self
                .handle_get_references_to_symbol_in_file(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_REFERENCED_SYMBOLS_FOR_NODE.0 => self
                .handle_get_referenced_symbols_for_node(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_SIGNATURE_USAGES.0 => self
                .handle_get_signature_usages(ctx, assert_params(&parsed))
                .map(to_any),
            m if m == Method::GET_COMPLETIONS_AT_POSITION.0 => self
                .handle_get_completions_at_position(ctx, assert_params(&parsed))
                .map(to_any),
            _ => Err(errors::errorf(format!("unknown method: {method}"), vec![])),
        }
    }

    // Go: api/session.go:609 HandleNotification
    // HandleNotification implements Handler.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: JsonValue,
    ) -> Result<(), GoError> {
        // TODO: Implement notification handling
        Ok(())
    }
}

impl Session {
    // Go: api/session.go handleBatchRequests (ts#63937)
    pub fn handle_batch_requests(
        &self,
        ctx: &Context,
        params: &BatchRequestsParams,
    ) -> Result<BatchRequestsResponse, GoError> {
        let mut responses = Vec::with_capacity(params.requests.len());
        for request in &params.requests {
            responses.push(self.handle_batch_request(ctx, request));
        }
        Ok(BatchRequestsResponse { responses })
    }

    // Go: api/session.go handleBatchRequest (ts#63937)
    // PORT: Go recovers a panic in a deferred function; `catch_unwind` covers
    // the same call. Go `debug.Stack()` is the backtrace at the recover point.
    pub fn handle_batch_request(&self, ctx: &Context, request: &BatchRequest) -> BatchResponse {
        let mut response = BatchResponse {
            method: request.method.clone(),
            ..Default::default()
        };
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ipc::Handler::handle_request(self, ctx, &request.method.0, request.params.clone())
        }));
        match outcome {
            Ok(Ok(result)) => response.result = result,
            Ok(Err(err)) => response.error = err.error(),
            Err(recovered) => {
                response.result = None;
                response.error = format!(
                    "panic: {}\n{}",
                    ipc::conn::recovered_value(recovered.as_ref()),
                    std::backtrace::Backtrace::force_capture()
                );
            }
        }
        response
    }
}

impl Session {
    // Go: api/session.go:579 handleStartCPUProfile
    pub fn handle_start_cpu_profile(
        &self,
        _ctx: &Context,
        params: Option<&ProfileParams>,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let Some(params) = params.filter(|params| !params.dir.is_empty()) else {
            return Err(errors::errorf(
                format!("{}: dir is required", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        if let Err(err) = self.cpu_profiler.start_cpu_profile(&params.dir) {
            return Err(errors::errorf(
                format!(
                    "{}: failed to start CPU profile: {}",
                    *ERR_CLIENT_ERROR, err
                ),
                vec![ERR_CLIENT_ERROR.clone(), err],
            ));
        }
        Ok(None)
    }

    // Go: api/session.go:589 handleStopCPUProfile
    pub fn handle_stop_cpu_profile(&self, _ctx: &Context) -> Result<ProfileResult, GoError> {
        match self.cpu_profiler.stop_cpu_profile() {
            Ok(file_path) => Ok(ProfileResult { file: file_path }),
            Err(err) => Err(errors::errorf(
                format!("{}: failed to stop CPU profile: {}", *ERR_CLIENT_ERROR, err),
                vec![ERR_CLIENT_ERROR.clone(), err],
            )),
        }
    }

    // Go: api/session.go:597 handleSaveHeapProfile
    pub fn handle_save_heap_profile(
        &self,
        _ctx: &Context,
        params: Option<&ProfileParams>,
    ) -> Result<ProfileResult, GoError> {
        let Some(params) = params.filter(|params| !params.dir.is_empty()) else {
            return Err(errors::errorf(
                format!("{}: dir is required", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        match crate::pprof::save_heap_profile(&params.dir) {
            Ok(file_path) => Ok(ProfileResult { file: file_path }),
            Err(err) => Err(errors::errorf(
                format!(
                    "{}: failed to save heap profile: {}",
                    *ERR_CLIENT_ERROR, err
                ),
                vec![ERR_CLIENT_ERROR.clone(), err],
            )),
        }
    }

    // Go: api/session.go:614 handleInitialize
    pub fn handle_initialize(&self, _ctx: &Context) -> Result<InitializeResponse, GoError> {
        Ok(InitializeResponse {
            use_case_sensitive_file_names: self
                .project_session
                .fs()
                .use_case_sensitive_file_names(),
            current_directory: self.project_session.get_current_directory(),
        })
    }

    // Go: api/session.go:827 handleUpdateSnapshot
    // handleUpdateSnapshot creates a new snapshot, optionally opening or closing
    // projects and files. With no args, it adopts the latest LSP state. Opens and
    // closes are ref-counted per session: the session holds at most one ref per
    // project/file, so repeated opens are idempotent and a close only releases a ref
    // the session is actually holding.
    // PORT: the Go `updateMu` lock is not ported (one thread).
    pub fn handle_update_snapshot(
        &self,
        ctx: &Context,
        params: &UpdateSnapshotParams,
    ) -> Result<UpdateSnapshotResponse, GoError> {
        let file_changes = self.to_file_change_summary(params.file_changes.as_ref());

        let mut api_request = project::APISnapshotRequest::default();
        let cwd = self.project_session.get_current_directory();

        // Open projects: only take a new ref for projects we aren't already holding open.
        let mut opened_projects: Vec<tspath::Path> = Vec::new();
        for p in &params.open_projects {
            let config_file_name = p.to_absolute_file_name(&cwd);
            let config_path = self.to_path(&config_file_name);
            if self.open_projects.borrow().contains(&config_path) {
                continue;
            }
            api_request
                .open_projects
                .get_or_insert_with(|| {
                    FxHashSet::with_capacity_and_hasher(
                        params.open_projects.len(),
                        Default::default(),
                    )
                })
                .insert(config_file_name);
            opened_projects.push(config_path);
        }

        // Close projects: only release a ref we currently hold.
        let mut closed_projects: Vec<tspath::Path> = Vec::new();
        for p in &params.close_projects {
            let config_path = self.to_path(&p.to_absolute_file_name(&cwd));
            if !self.open_projects.borrow().contains(&config_path) {
                continue;
            }
            api_request
                .close_projects
                .get_or_insert_with(|| {
                    FxHashSet::with_capacity_and_hasher(
                        params.close_projects.len(),
                        Default::default(),
                    )
                })
                .insert(config_path.clone());
            closed_projects.push(config_path);
        }

        // Open files: only open files we aren't already holding open, so each file is
        // held by at most one API ref from this session.
        let mut opened_files: Vec<tspath::Path> = Vec::new();
        for f in &params.open_files {
            let uri = f.to_uri(&cwd);
            let path = self.to_path(&uri.file_name());
            if self.open_files.borrow().contains(&path) {
                continue;
            }
            api_request
                .open_files
                .get_or_insert_with(|| IndexSet::with_capacity(params.open_files.len()))
                .insert(uri);
            opened_files.push(path);
        }

        // Close files: only release a ref we currently hold.
        let mut closed_files: Vec<tspath::Path> = Vec::new();
        for f in &params.close_files {
            let path = self.to_path(&f.to_uri(&cwd).file_name());
            if !self.open_files.borrow().contains(&path) {
                continue;
            }
            api_request
                .close_files
                .get_or_insert_with(|| {
                    FxHashSet::with_capacity_and_hasher(
                        params.close_files.len(),
                        Default::default(),
                    )
                })
                .insert(path.clone());
            closed_files.push(path);
        }

        // Even when nothing is opened or closed, APIUpdate ensures all projects and
        // files opened by the API are up to date. For an API connected to an LSP server,
        // this brings the API state up to date with the LSP state and ensures projects
        // the API cares about are ready to be queried.
        let (snapshot, err) = self
            .project_session
            .api_update(ctx, &file_changes, api_request);
        if let Some(err) = err {
            // APIUpdate returns a ref'd snapshot even on error; release it.
            project::Snapshot::deref(&snapshot, &self.project_session);
            return Err(errors::errorf(
                format!("{}: failed to update snapshot: {}", *ERR_CLIENT_ERROR, err),
                vec![ERR_CLIENT_ERROR.clone(), err],
            ));
        }

        // Commit ref tracking now that the update succeeded.
        {
            let mut open_projects = self.open_projects.borrow_mut();
            for config_path in opened_projects {
                open_projects.insert(config_path);
            }
            for config_path in &closed_projects {
                open_projects.remove(config_path);
            }
        }
        {
            let mut open_files = self.open_files.borrow_mut();
            for path in opened_files {
                open_files.insert(path);
            }
            for path in &closed_files {
                open_files.remove(path);
            }
        }

        // Create or ref-count snapshot data, then atomically read the previous latest
        // snapshot (the diff base) and advance latestSnapshot to the new handle.
        // If the same snapshot ID is returned (no changes), we increment the ref count
        // so each client-side Snapshot can be disposed independently.
        let handle = snapshot_handle(&snapshot);
        let existing = self.snapshots.borrow().get(&handle).cloned();
        if let Some(sd) = existing {
            // Same snapshot already stored — release the caller's ref since
            // the stored snapshot already has one, and bump the API refcount.
            project::Snapshot::deref(&snapshot, &self.project_session);
            sd.ref_count.set(sd.ref_count.get() + 1);
        } else {
            let sd = Rc::new(SnapshotData {
                snapshot: snapshot.clone(),
                ref_count: Cell::new(1),
                symbol_registry: RefCell::new(FxHashMap::default()),
                symbol_canonical_projects: RefCell::new(FxHashMap::default()),
                project_registries: RefCell::new(FxHashMap::default()),
            });
            self.snapshots.borrow_mut().insert(handle, sd);
        }
        let prev_sd = self
            .snapshots
            .borrow()
            .get(&self.latest_snapshot.get())
            .cloned();
        self.latest_snapshot.set(handle);

        // Build projects list
        let projects = snapshot.project_collection.projects();
        let mut project_responses = Vec::with_capacity(projects.len());
        for proj in &projects {
            if proj.borrow().command_line.is_none() {
                continue;
            }
            project_responses.push(new_project_response(&proj.borrow()));
        }

        // Compute changes from the previous latest snapshot
        let mut changes: Option<SnapshotChanges> = None;
        if let Some(prev_sd) = prev_sd {
            changes = Some(compute_snapshot_changes(&prev_sd.snapshot, &snapshot));
        }

        Ok(UpdateSnapshotResponse {
            snapshot: handle,
            projects: project_responses,
            changes,
        })
    }

    // Go: api/session.go:1076 handleUpdateTemporarySnapshot (tsgo#4642)
    // handleUpdateTemporarySnapshot creates a temporary snapshot that overrides the
    // content of a single file, without opening/closing any projects or files and
    // without advancing the session's latest snapshot.
    // PORT: Go `defer func() { _ = s.releaseSnapshot(params.Snapshot) }()`: the
    // body runs in a closure, and the release runs after it on every path.
    pub fn handle_update_temporary_snapshot(
        &self,
        ctx: &Context,
        params: &UpdateTemporarySnapshotParams,
    ) -> Result<UpdateSnapshotResponse, GoError> {
        let base_sd = self.retain_snapshot_data(params.snapshot)?;
        let result = (|| {
            let uri = params
                .file
                .to_uri(&self.project_session.get_current_directory());

            let snapshot = match self.project_session.api_update_temporary(
                ctx,
                &base_sd.snapshot,
                &uri,
                params.new_text.clone(),
            ) {
                Ok(snapshot) => snapshot,
                Err(err) => {
                    return Err(errors::errorf(
                        format!(
                            "{}: failed to update temporary snapshot: {}",
                            *ERR_CLIENT_ERROR, err
                        ),
                        vec![ERR_CLIENT_ERROR.clone(), err],
                    ));
                }
            };

            let handle = snapshot_handle(&snapshot);
            let existing = self.snapshots.borrow().get(&handle).cloned();
            if let Some(sd) = existing {
                project::Snapshot::deref(&snapshot, &self.project_session);
                sd.ref_count.set(sd.ref_count.get() + 1);
            } else {
                let sd = Rc::new(SnapshotData {
                    snapshot: snapshot.clone(),
                    ref_count: Cell::new(1),
                    symbol_registry: RefCell::new(FxHashMap::default()),
                    symbol_canonical_projects: RefCell::new(FxHashMap::default()),
                    project_registries: RefCell::new(FxHashMap::default()),
                });
                self.snapshots.borrow_mut().insert(handle, sd);
            }

            // Build projects list
            let projects = snapshot.project_collection.projects();
            let mut project_responses = Vec::with_capacity(projects.len());
            for proj in &projects {
                if proj.borrow().command_line.is_none() {
                    continue;
                }
                project_responses.push(new_project_response(&proj.borrow()));
            }

            // Compute changes from the requested base snapshot so the client can retain
            // cached source files for unchanged files.
            let changes = compute_snapshot_changes(&base_sd.snapshot, &snapshot);

            Ok(UpdateSnapshotResponse {
                snapshot: handle,
                projects: project_responses,
                changes: Some(changes),
            })
        })();
        let _ = self.release_snapshot(params.snapshot);
        result
    }

    // Go: api/session.go:699 handleRelease
    // handleRelease decrements the ref count for a snapshot.
    // The snapshot and its registries are only cleaned up when the ref count reaches zero.
    pub fn handle_release(
        &self,
        _ctx: &Context,
        params: Option<&ReleaseParams>,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let Some(params) = params.filter(|params| params.snapshot.0 != 0) else {
            return Err(errors::errorf(
                format!("{}: empty handle", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };

        self.release_snapshot(params.snapshot)?;
        Ok(to_any(true))
    }

    // Go: api/session.go:997 handleGetDefaultProjectForFile
    // handleGetDefaultProjectForFile returns the default project for a given file,
    // or nil if no project currently contains the file.
    pub fn handle_get_default_project_for_file(
        &self,
        _ctx: &Context,
        params: &GetDefaultProjectForFileParams,
    ) -> Result<Option<ProjectResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let uri = params
            .file
            .to_uri(&self.project_session.get_current_directory());
        let proj = sd.snapshot.get_default_project(&uri);
        let Some(proj) = proj else {
            return Ok(None);
        };

        Ok(Some(new_project_response(&proj.borrow())))
    }

    // Go: api/session.go:1161 handleParseCommandLine
    // handleParseCommandLine parses command-line arguments.
    pub fn handle_parse_command_line(
        &self,
        _ctx: &Context,
        params: &ParseCommandLineParams,
    ) -> Result<Option<ConfigFileResponse>, GoError> {
        Ok(new_config_file_response(Some(
            &tsoptions::parse_command_line(&params.command_line, &*self.project_session),
        )))
    }

    // Go: api/session.go:1166 handleReadConfigFile
    // handleReadConfigFile reads and parses a JSON configuration file.
    pub fn handle_read_config_file(
        &self,
        _ctx: &Context,
        params: &ReadConfigFileParams,
    ) -> Result<ReadConfigFileResponse, GoError> {
        let config_file_name = params
            .file
            .to_absolute_file_name(&self.project_session.get_current_directory());
        let (config_file_content, ok) = self.project_session.fs().read_file(&config_file_name);
        if !ok {
            return Ok(ReadConfigFileResponse {
                config: tsoptions::CompilerOptionsValue::Map(IndexMap::new()),
                error: Some(new_diagnostic_response(&new_compiler_diagnostic(
                    diag::Cannot_read_file_0,
                    args![config_file_name],
                ))),
            });
        }

        let (config, parse_errors) = tsoptions::parse_config_file_text_to_json(
            &config_file_name,
            self.to_path(&config_file_name),
            &config_file_content,
        );
        let mut response = ReadConfigFileResponse {
            config,
            error: None,
        };
        if !parse_errors.is_empty() {
            response.error = Some(new_diagnostic_response(&parse_errors[0]));
        }
        Ok(response)
    }

    // Go: api/session.go:1189 handleParseJsonConfigFileContent
    // handleParseJsonConfigFileContent parses an in-memory JSON configuration.
    pub fn handle_parse_json_config_file_content(
        &self,
        _ctx: &Context,
        params: &ParseJsonConfigFileContentParams,
    ) -> Result<Option<ConfigFileResponse>, GoError> {
        if params.config_directory.is_none() == params.config_file_name.is_none() {
            return Err(errors::errorf(
                format!(
                    "{}: exactly one of configDirectory or configFileName is required",
                    *ERR_CLIENT_ERROR
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let base_path;
        let mut config_file_name = String::new();
        if let Some(config_directory) = &params.config_directory {
            base_path = tspath::get_normalized_absolute_path(
                config_directory,
                &self.project_session.get_current_directory(),
            );
        } else {
            config_file_name = params
                .config_file_name
                .as_ref()
                .expect("configFileName is set")
                .to_absolute_file_name(&self.project_session.get_current_directory());
            base_path = tspath::get_directory_path(&config_file_name);
        }

        let parsed_command_line = tsoptions::parse_json_config_file_content(
            &json_value_to_any(&params.json),
            &*self.project_session,
            &base_path,
            None, /*existingOptions*/
            &config_file_name,
            &[],  /*resolutionStack*/
            None, /*extendedConfigCache*/
        );
        Ok(new_config_file_response(Some(&parsed_command_line)))
    }

    // Go: api/session.go:737 handleParseConfigFile
    // handleParseConfigFile parses a tsconfig.json file and returns its contents.
    pub fn handle_parse_config_file(
        &self,
        _ctx: &Context,
        params: &ParseConfigFileParams,
    ) -> Result<ConfigFileResponse, GoError> {
        let config_file_name = params
            .file
            .to_absolute_file_name(&self.project_session.get_current_directory());
        let (config_file_content, ok) = self.project_session.fs().read_file(&config_file_name);
        if !ok {
            return Err(errors::errorf(
                format!(
                    "{}: could not read file {}",
                    *ERR_CLIENT_ERROR,
                    gostd::strconv::quote(&config_file_name)
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let config_dir = tspath::get_directory_path(&config_file_name);
        let ts_config_source_file = tsoptions::new_tsconfig_source_file_from_file_path(
            &config_file_name,
            self.to_path(&config_file_name),
            &config_file_content,
        );
        let parsed_command_line = tsoptions::parse_json_source_file_config_file_content(
            ts_config_source_file,
            &*self.project_session,
            &config_dir,
            None, /*existingOptions*/
            None, /*existingOptionsRaw*/
            &config_file_name,
            &[],  /*resolutionStack*/
            None, /*extendedConfigCache*/
        );

        // PORT: Go returns a `*ConfigFileResponse` that is never nil here.
        Ok(new_config_file_response(Some(&parsed_command_line))
            .expect("NewConfigFileResponse of a parsed command line"))
    }

    // Go: api/session.go:1242 handleTranspile (tsgo#4849)
    pub fn handle_transpile(
        &self,
        ctx: &Context,
        params: &TranspileParams,
        declaration: bool,
    ) -> Result<TranspileOutputResponse, GoError> {
        transpile_output(ctx, &params.input, &params.options, declaration)
    }

    // Go: api/session.go:1246 handleTranspileFromFile (tsgo#4849)
    pub fn handle_transpile_from_file(
        &self,
        ctx: &Context,
        params: &TranspileFromFileParams,
        declaration: bool,
    ) -> Result<TranspileOutputResponse, GoError> {
        let file_name = tspath::get_normalized_absolute_path(
            &params.file_name,
            &self.project_session.get_current_directory(),
        );
        let (input, ok) = self.project_session.fs().read_file(&file_name);
        if !ok {
            return Err(errors::errorf(
                format!(
                    "{}: could not read file {}",
                    *ERR_CLIENT_ERROR,
                    gostd::strconv::quote(&file_name)
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        let mut options = params.options.clone();
        options.file_name = file_name;
        transpile_output(ctx, &input, &options, declaration)
    }
}

// Go: api/session.go:1257 transpileOutput (tsgo#4849)
fn transpile_output(
    ctx: &Context,
    input: &str,
    options: &TranspileOptions,
    declaration: bool,
) -> Result<TranspileOutputResponse, GoError> {
    let transpile_options = transpile::Options {
        compiler_options: options.compiler_options.clone(),
        file_name: options.file_name.clone(),
        report_diagnostics: options.report_diagnostics,
    };
    let output = if declaration {
        transpile::transpile_declaration(ctx, input, transpile_options)
    } else {
        transpile::transpile_module(ctx, input, transpile_options)
    };
    let Some(output) = output else {
        if let Some(err) = ctx.err() {
            return Err(err);
        }
        return Err(errors::new("transpilation produced no output"));
    };
    Ok(TranspileOutputResponse {
        output_text: output.output_text,
        diagnostics: new_diagnostic_responses(&output.diagnostics),
        source_map_text: output.source_map_text,
    })
}

impl Session {
    // Go: api/session.go:769 handleGetSourceFile
    // handleGetSourceFile returns a source file from a project within a snapshot.
    pub fn handle_get_source_file(
        &self,
        _ctx: &Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = &sd.get_program(&params.project)?;
        // The encoder reads lazy JSDoc (file header, "Current program").
        let _program = ls_program::enter(program);

        self.encode_source_file_response(
            program
                .get_source_file(&params.file.to_file_name())
                .map_or(Node::NIL, |f| f.root),
        )
    }

    // Go: api/session.go:1301 handleGetConfigFileNames
    // handleGetConfigFileNames returns tsconfig file names associated with the project's command line.
    // PORT: Go `program.CommandLine()` is never nil in the port.
    pub fn handle_get_config_file_names(
        &self,
        _ctx: &Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<String>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;

        let command_line = program.command_line();
        let Some(config_file) = command_line
            .config_file
            .as_ref()
            .filter(|f| f.source_file.is_some())
        else {
            return Ok(Vec::new());
        };

        let extended_files = command_line.extended_source_files();
        let mut config_files = Vec::with_capacity(extended_files.len() + 1);
        config_files.push(config_file.file_name.clone());
        config_files.extend(extended_files.iter().cloned());
        Ok(config_files)
    }

    // Go: api/session.go:1327 handleGetConfigSourceFile
    // handleGetConfigSourceFile returns a tsconfig source file associated with the project's command line.
    pub fn handle_get_config_source_file(
        &self,
        _ctx: &Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;
        // The encoder reads lazy JSDoc (file header, "Current program").
        let _program = ls_program::enter(&program);

        let command_line = program.command_line();
        let Some(root_config_source_file) = command_line
            .config_file
            .as_ref()
            .filter(|f| f.source_file.is_some())
        else {
            return self.encode_source_file_response(Node::NIL);
        };

        let requested_path = tspath::to_path(
            &params.file.to_file_name(),
            &program.get_current_directory(),
            program.use_case_sensitive_file_names(),
        );
        if root_config_source_file.path == requested_path {
            return self.encode_source_file_response(root_config_source_file.source_file);
        }

        for config_file_name in command_line.extended_source_files() {
            if tspath::to_path(
                config_file_name,
                &program.get_current_directory(),
                program.use_case_sensitive_file_names(),
            ) != requested_path
            {
                continue;
            }

            let (config_file_content, ok) = sd.snapshot.read_file(config_file_name);
            if !ok {
                return self.encode_source_file_response(Node::NIL);
            }

            let config_source_file = tsoptions::new_tsconfig_source_file_from_file_path(
                config_file_name,
                requested_path,
                &config_file_content,
            );
            return self.encode_source_file_response(config_source_file.source_file);
        }

        self.encode_source_file_response(Node::NIL)
    }

    // Go: api/session.go:1366 encodeSourceFileResponse
    // PORT: Go `*ast.SourceFile` is the root node; `Node::NIL` is nil.
    pub fn encode_source_file_response(
        &self,
        source_file: Node,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        if source_file.is_nil() {
            if self.use_binary_responses {
                return Ok(to_any(RawBinary(Vec::new())));
            }
            return Ok(None);
        }

        // Encode the full source file.
        let data = match encoder::encode_source_file(source_file) {
            Ok((data, _)) => data,
            Err(err) => {
                return Err(errors::errorf(
                    format!("failed to encode source file: {err}"),
                    vec![err],
                ));
            }
        };

        if self.use_binary_responses {
            return Ok(to_any(RawBinary(data)));
        }
        Ok(to_any(SourceFileResponse {
            data: base64_std_encoding_encode_to_string(&data),
        }))
    }

    // Go: api/session.go:1080 handleGetSourceFileNames
    // handleGetSourceFileNames returns file names of all source files in a project.
    pub fn handle_get_source_file_names(
        &self,
        _ctx: &Context,
        params: &GetSourceFileNamesParams,
    ) -> Result<Vec<String>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = &sd.get_program(&params.project)?;

        let source_files = program.get_source_files();
        let mut result = Vec::with_capacity(source_files.len());
        for source_file in source_files {
            result.push(source_file.file_name().to_string());
        }
        Ok(result)
    }

    // Go: api/session.go:1068 handleGetSourceFileMetadata
    // handleGetSourceFileMetadata returns program-stored metadata for a single source file.
    // The client fetches this lazily per file and caches it.
    pub fn handle_get_source_file_metadata(
        &self,
        _ctx: &Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<SourceFileMetadata>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = &sd.get_program(&params.project)?;

        let Some(source_file) = program.get_source_file(&params.file.to_file_name()) else {
            return Ok(None);
        };

        let meta_data = program.get_source_file_meta_data(source_file.path());
        Ok(Some(SourceFileMetadata {
            is_default_library: program.is_source_file_default_library(source_file.path()),
            is_from_external_library: program.is_source_file_from_external_library(&source_file),
            package_json_type: meta_data.package_json_type,
            package_json_directory: meta_data.package_json_directory,
            implied_node_format: meta_data.implied_node_format.0,
        }))
    }

    // Go: api/session.go:804 handleGetSymbolAtPosition
    // handleGetSymbolAtPosition returns the symbol at a position in a file.
    pub fn handle_get_symbol_at_position(
        &self,
        ctx: &Context,
        params: &GetSymbolAtPositionParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let position_map = source_file_get_position_map(source_file);
        let node = astnav::get_touching_property_name(
            source_file,
            position_map.utf16_to_utf8(params.position as i32),
        );
        if node.is_nil() {
            return Ok(None);
        }

        let symbol = setup
            .checker
            .borrow_mut()
            .get_symbol_at_location_exported(node);
        if symbol.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:1468 handleGetSymbolOfSourceFile
    // handleGetSymbolOfSourceFile returns the module symbol for a source file, if any.
    // For non-module (script) files, returns nil.
    pub fn handle_get_symbol_of_source_file(
        &self,
        ctx: &Context,
        params: &GetSymbolOfSourceFileParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let symbol = setup
            .checker
            .borrow_mut()
            .get_symbol_at_location_exported(source_file);
        if symbol.is_nil() {
            return Ok(None);
        }
        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:1488 handleGetSymbolsOfSourceFiles
    // handleGetSymbolsOfSourceFiles returns the module symbols for multiple source files.
    pub fn handle_get_symbols_of_source_files(
        &self,
        ctx: &Context,
        params: &GetSymbolsOfSourceFilesParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let mut results: Vec<Option<SymbolResponse>> =
            (0..params.files.len()).map(|_| None).collect();
        for (i, file) in params.files.iter().enumerate() {
            let source_file = setup
                .program
                .get_source_file(&file.to_file_name())
                .map_or(Node::NIL, |f| f.root);
            if source_file.is_nil() {
                return Err(errors::errorf(
                    format!(
                        "{}: source file not found: {}",
                        *ERR_CLIENT_ERROR,
                        file.string()
                    ),
                    vec![ERR_CLIENT_ERROR.clone()],
                ));
            }
            let symbol = setup
                .checker
                .borrow_mut()
                .get_symbol_at_location_exported(source_file);
            if symbol.is_some() {
                results[i] = setup.new_symbol_response(symbol);
            }
        }
        Ok(results)
    }

    // Go: api/session.go:831 handleGetSymbolsAtPositions
    // handleGetSymbolsAtPositions returns symbols at multiple positions in a file.
    pub fn handle_get_symbols_at_positions(
        &self,
        ctx: &Context,
        params: &GetSymbolsAtPositionsParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let position_map = source_file_get_position_map(source_file);
        let mut results: Vec<Option<SymbolResponse>> =
            (0..params.positions.len()).map(|_| None).collect();
        for (i, &pos) in params.positions.iter().enumerate() {
            let node = astnav::get_touching_property_name(
                source_file,
                position_map.utf16_to_utf8(pos as i32),
            );
            if node.is_nil() {
                continue;
            }
            let symbol = setup
                .checker
                .borrow_mut()
                .get_symbol_at_location_exported(node);
            if symbol.is_some() {
                results[i] = setup.new_symbol_response(symbol);
            }
        }

        Ok(results)
    }

    // Go: api/session.go:860 handleGetSymbolAtLocation
    // handleGetSymbolAtLocation returns the symbol at a node location.
    pub fn handle_get_symbol_at_location(
        &self,
        ctx: &Context,
        params: &GetSymbolAtLocationParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(None);
        }

        let symbol = setup
            .checker
            .borrow_mut()
            .get_symbol_at_location_exported(node);
        if symbol.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:884 handleGetSymbolsAtLocations
    // handleGetSymbolsAtLocations returns symbols at multiple node locations.
    pub fn handle_get_symbols_at_locations(
        &self,
        ctx: &Context,
        params: &GetSymbolsAtLocationsParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let mut results: Vec<Option<SymbolResponse>> =
            (0..params.locations.len()).map(|_| None).collect();
        for (i, loc) in params.locations.iter().enumerate() {
            let node = setup.sd.resolve_node_handle(&setup.program, loc)?;
            if node.is_nil() {
                continue;
            }
            let symbol = setup
                .checker
                .borrow_mut()
                .get_symbol_at_location_exported(node);
            if symbol.is_some() {
                results[i] = setup.new_symbol_response(symbol);
            }
        }

        Ok(results)
    }

    // Go: api/session.go:910 handleGetTypeOfSymbol
    // handleGetTypeOfSymbol returns the type of a symbol.
    pub fn handle_get_type_of_symbol(
        &self,
        ctx: &Context,
        params: &GetTypeOfSymbolParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let t = setup
            .checker
            .borrow_mut()
            .get_type_of_symbol_exported(symbol);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:934 handleGetTypesOfSymbols
    // handleGetTypesOfSymbols returns the types of multiple symbols.
    pub fn handle_get_types_of_symbols(
        &self,
        ctx: &Context,
        params: &GetTypesOfSymbolsParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let mut results: Vec<Option<TypeResponse>> =
            (0..params.symbols.len()).map(|_| None).collect();
        for (i, &sym_handle) in params.symbols.iter().enumerate() {
            let (owner, symbol) = setup.resolve_symbol_handle(sym_handle)?;
            let symbol = checker_symbol(&setup.checker, &owner, symbol);
            // resolveSymbolHandle errors on an unresolvable handle and GetTypeOfSymbol
            // never returns nil, so every element resolves to a type (error type at worst).
            let t = setup
                .checker
                .borrow_mut()
                .get_type_of_symbol_exported(symbol);
            results[i] = setup.new_type_response(t);
        }

        Ok(results)
    }

    // Go: api/session.go:960 handleGetDeclaredTypeOfSymbol
    // handleGetDeclaredTypeOfSymbol returns the declared type of a symbol (e.g. the type alias body for type alias symbols).
    pub fn handle_get_declared_type_of_symbol(
        &self,
        ctx: &Context,
        params: &GetTypeOfSymbolParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let t = setup
            .checker
            .borrow_mut()
            .get_declared_type_of_symbol_exported(symbol);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:984 handleResolveName
    // handleResolveName resolves a name to a symbol at a given location.
    pub fn handle_resolve_name(
        &self,
        ctx: &Context,
        params: &ResolveNameParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        // Resolve location node - either from node handle or from fileName+position
        let location =
            setup.resolve_location(&params.location, params.file.as_ref(), params.position)?;

        let symbol = setup.checker.borrow_mut().resolve_name_exported(
            &params.name,
            location,
            SymbolFlags(params.meaning),
            params.exclude_globals,
        );
        if symbol.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:1667 handleGetSymbolsInScope
    // handleGetSymbolsInScope returns all symbols with the given meaning that are visible at a location.
    // PORT: Go builds the list from Go maps, so its order is random; the
    // port's order is stable (`Checker::get_symbols_in_scope`).
    pub fn handle_get_symbols_in_scope(
        &self,
        ctx: &Context,
        params: &GetSymbolsInScopeParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let location =
            setup.resolve_location(&params.location, params.file.as_ref(), params.position)?;
        if location.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: getSymbolsInScope requires a location",
                    *ERR_CLIENT_ERROR
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let symbols = setup
            .checker
            .borrow_mut()
            .get_symbols_in_scope_exported(location, SymbolFlags(params.meaning));
        let mut results = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            results.push(setup.new_symbol_response(symbol));
        }

        Ok(results)
    }

    // Go: api/session.go:1015 handleGetSignaturesOfType
    // handleGetSignaturesOfType returns the call or construct signatures of a type.
    pub fn handle_get_signatures_of_type(
        &self,
        ctx: &Context,
        params: &GetSignaturesOfTypeParams,
    ) -> Result<Vec<Option<SignatureResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let sigs = setup
            .checker
            .borrow_mut()
            .get_signatures_of_type_exported(t, SignatureKind(params.kind));
        let mut results = Vec::with_capacity(sigs.len());
        for sig in sigs {
            results.push(setup.new_signature_response(sig));
        }

        Ok(results)
    }

    // Go: api/session.go:1037 handleGetResolvedSignature
    // handleGetResolvedSignature returns the resolved signature of a call-like expression.
    pub fn handle_get_resolved_signature(
        &self,
        ctx: &Context,
        params: &GetResolvedSignatureParams,
    ) -> Result<Option<SignatureResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let sig = setup
            .checker
            .borrow_mut()
            .get_resolved_signature_exported(node);
        Ok(setup.new_signature_response(sig))
    }

    // Go: api/session.go:1057 handleGetTypeAtLocation
    // handleGetTypeAtLocation returns the type at a node location.
    pub fn handle_get_type_at_location(
        &self,
        ctx: &Context,
        params: &GetTypeAtLocationParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let t = setup.checker.borrow_mut().get_type_at_location(node);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1081 handleGetTypeAtLocations
    // handleGetTypeAtLocations returns types at multiple node locations.
    pub fn handle_get_type_at_locations(
        &self,
        ctx: &Context,
        params: &GetTypeAtLocationsParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let mut results: Vec<Option<TypeResponse>> =
            (0..params.locations.len()).map(|_| None).collect();
        for (i, loc) in params.locations.iter().enumerate() {
            let node = setup.sd.resolve_node_handle(&setup.program, loc)?;
            // resolveNodeHandle errors on an unresolvable handle and GetTypeAtLocation
            // never returns nil, so every element resolves to a type (error type at worst).
            let t = setup.checker.borrow_mut().get_type_at_location(node);
            results[i] = setup.new_type_response(t);
        }

        Ok(results)
    }

    // Go: api/session.go:1107 handleGetTypeAtPosition
    // handleGetTypeAtPosition returns the type at a position in a file.
    pub fn handle_get_type_at_position(
        &self,
        ctx: &Context,
        params: &GetTypeAtPositionParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let position_map = source_file_get_position_map(source_file);
        let node = astnav::get_touching_property_name(
            source_file,
            position_map.utf16_to_utf8(params.position as i32),
        );
        if node.is_nil() {
            return Ok(None);
        }

        let t = setup.checker.borrow_mut().get_type_at_location(node);
        if t.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1134 handleGetTypesAtPositions
    // handleGetTypesAtPositions returns types at multiple positions in a file.
    pub fn handle_get_types_at_positions(
        &self,
        ctx: &Context,
        params: &GetTypesAtPositionsParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let position_map = source_file_get_position_map(source_file);
        let mut results: Vec<Option<TypeResponse>> =
            (0..params.positions.len()).map(|_| None).collect();
        for (i, &pos) in params.positions.iter().enumerate() {
            let node = astnav::get_touching_property_name(
                source_file,
                position_map.utf16_to_utf8(pos as i32),
            );
            if node.is_nil() {
                continue;
            }
            let t = setup.checker.borrow_mut().get_type_at_location(node);
            if t.is_some() {
                results[i] = setup.new_type_response(t);
            }
        }

        Ok(results)
    }

    // Go: api/session.go:1162 handleGetParentOfSymbol
    pub fn handle_get_parent_of_symbol(
        &self,
        _ctx: &Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        self.resolve_symbol_property_of_symbol(params, &|c: &Checker, sym: SymbolId| {
            c.sym(sym).parent
        })
    }

    // Go: api/session.go:1166 handleGetMembersOfSymbol
    pub fn handle_get_members_of_symbol(
        &self,
        ctx: &Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        self.resolve_symbol_table_property_of_symbol(
            ctx,
            params,
            &|c: &Checker, symbol: SymbolId| c.sym(symbol).members,
        )
    }

    // Go: api/session.go:1172 handleGetExportsOfSymbol
    pub fn handle_get_exports_of_symbol(
        &self,
        ctx: &Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        self.resolve_symbol_table_property_of_symbol(
            ctx,
            params,
            &|c: &Checker, symbol: SymbolId| c.sym(symbol).exports,
        )
    }

    // Go: api/session.go:1178 handleGetExportSymbolOfSymbol
    pub fn handle_get_export_symbol_of_symbol(
        &self,
        _ctx: &Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        self.resolve_symbol_property_of_symbol(params, &|c: &Checker, sym: SymbolId| {
            c.sym(sym).export_symbol
        })
    }

    // Go: api/session.go:1182 handleGetSymbolOfType
    pub fn handle_get_symbol_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        self.resolve_symbol_property_of_type(params, &|c: &Checker, t: TypeId| c.ty(t).symbol())
    }

    // Go: api/session.go:1186 handleGetTargetOfType
    pub fn handle_get_target_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| c.ty(t).target())
    }

    // Go: api/session.go:1190 handleGetFreshTypeOfType
    pub fn handle_get_fresh_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_literal_type().fresh_type()
        })
    }

    // Go: api/session.go:1194 handleGetRegularTypeOfType
    pub fn handle_get_regular_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_literal_type().regular_type()
        })
    }

    // Go: api/session.go:1198 handleGetTypesOfType
    pub fn handle_get_types_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).types().to_vec()
        })
    }

    // Go: api/session.go:1202 handleGetTypeParametersOfType
    pub fn handle_get_type_parameters_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_interface_type().type_parameters().to_vec()
        })
    }

    // Go: api/session.go:1206 handleGetOuterTypeParametersOfType
    pub fn handle_get_outer_type_parameters_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_interface_type().outer_type_parameters().to_vec()
        })
    }

    // Go: api/session.go:1210 handleGetLocalTypeParametersOfType
    pub fn handle_get_local_type_parameters_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_interface_type().local_type_parameters().to_vec()
        })
    }

    // Go: api/session.go:1214 handleGetAliasTypeArgumentsOfType
    pub fn handle_get_alias_type_arguments_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_type(params, &|c: &Checker, t: TypeId| {
            let Some(alias) = c.ty(t).alias() else {
                return Vec::new();
            };
            alias.type_arguments().to_vec()
        })
    }

    // Go: api/session.go:1223 handleGetAliasSymbolOfType
    pub fn handle_get_alias_symbol_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        self.resolve_symbol_property_of_type(params, &|c: &Checker, t: TypeId| {
            let Some(alias) = c.ty(t).alias() else {
                return SymbolId::NIL;
            };
            alias.symbol()
        })
    }

    // Go: api/session.go:1232 handleGetObjectTypeOfType
    pub fn handle_get_object_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_indexed_access_type().object_type()
        })
    }

    // Go: api/session.go:1236 handleGetIndexTypeOfType
    pub fn handle_get_index_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_indexed_access_type().index_type()
        })
    }

    // Go: api/session.go:1240 handleGetCheckTypeOfType
    pub fn handle_get_check_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_conditional_type().check_type()
        })
    }

    // Go: api/session.go:1244 handleGetExtendsTypeOfType
    pub fn handle_get_extends_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_conditional_type().extends_type()
        })
    }

    // Go: api/session.go:1248 handleGetBaseTypeOfType
    pub fn handle_get_base_type_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_substitution_type().base_type()
        })
    }

    // Go: api/session.go:1252 handleGetConstraintOfType
    // handleGetConstraintOfType returns the constraint of a substitution type.
    // Type parameter constraints are handled by handleGetConstraintOfTypeParameter.
    pub fn handle_get_constraint_of_type(
        &self,
        _ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        self.resolve_type_property_of_type(params, &|c: &Checker, t: TypeId| {
            c.ty(t).as_substitution_type().subst_constraint()
        })
    }

    // Go: api/session.go:1256 handleGetTypeParametersOfSignature
    pub fn handle_get_type_parameters_of_signature(
        &self,
        _ctx: &Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        self.resolve_type_array_property_of_signature(params, &|c: &Checker, sig: SignatureId| {
            c.sig(sig).type_parameters().to_vec()
        })
    }

    // Go: api/session.go:1260 handleGetParametersOfSignature
    pub fn handle_get_parameters_of_signature(
        &self,
        _ctx: &Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        self.resolve_symbol_array_property_of_signature(params, &|c: &Checker, sig: SignatureId| {
            c.sig(sig).parameters().to_vec()
        })
    }

    // Go: api/session.go:1264 handleGetThisParameterOfSignature
    pub fn handle_get_this_parameter_of_signature(
        &self,
        _ctx: &Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        self.resolve_symbol_property_of_signature(params, &|c: &Checker, sig: SignatureId| {
            c.sig(sig).this_parameter()
        })
    }

    // Go: api/session.go:1268 handleGetTargetOfSignature
    pub fn handle_get_target_of_signature(
        &self,
        _ctx: &Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<SignatureResponse>, GoError> {
        self.resolve_signature_property_of_signature(params, &|c: &Checker, sig: SignatureId| {
            c.sig(sig).target()
        })
    }

    // Go: api/session.go:1953 handleGetImportAdderEdits (tsgo#3881, tsgo#4712)
    // PORT: Go returns `[]*TextEdit`, and `toAPITextEdits` can return nil
    // (JSON `null`); nil is `None`.
    // PORT: Go `defer preparedSnapshot.Deref(s.projectSession)` is the
    // `Release` guard `_deref_prepared`. It is declared before the checker
    // lease, so the lease (`defer done()`) ends first, as in Go. Go passes
    // `ch` to `NewImportAdder`; the port's adder takes the checker in
    // `AddImportFromExportedSymbol` (import_adder.rs header). A symbol handle
    // indexes the arena of the checker that made it, so `checker_symbol` maps
    // it into `ch` (file header).
    pub fn handle_get_import_adder_edits(
        &self,
        ctx: &Context,
        params: &GetImportAdderEditsParams,
    ) -> Result<Option<Vec<TextEdit>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let project_path = parse_project_handle(&params.project);
        let mut working_snapshot = sd.snapshot.clone();
        let mut program = sd.get_program(&params.project)?;
        let mut source_file = program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let mut user_preferences = working_snapshot.user_preferences();
        let mut _deref_prepared = ls_program::Release::noop();
        let registry = working_snapshot.auto_import_registry();
        if registry.is_none()
            || !autoimport::Registry::is_prepared_for_importing_file(
                registry.as_deref(),
                source_file_file_name(source_file),
                &project_path,
                &user_preferences,
            )
        {
            let prepared_snapshot = self.project_session.get_snapshot_with_auto_imports(
                ctx,
                &working_snapshot,
                &params
                    .file
                    .to_uri(&self.project_session.get_current_directory()),
            );
            _deref_prepared = {
                let (snapshot, session) = (prepared_snapshot.clone(), self.project_session.clone());
                ls_program::Release::new(move || project::Snapshot::deref(&snapshot, &session))
            };

            working_snapshot = prepared_snapshot;
            let proj = working_snapshot
                .project_collection
                .get_project_by_path(&project_path);
            let Some(proj) = proj else {
                return Err(errors::errorf(
                    format!(
                        "{}: project {} not found",
                        *ERR_CLIENT_ERROR,
                        project_path.as_str()
                    ),
                    vec![ERR_CLIENT_ERROR.clone()],
                ));
            };
            let proj_program = proj.borrow().get_program();
            let Some(proj_program) = proj_program else {
                return Err(errors::errorf(
                    format!("{}: project has no program", *ERR_CLIENT_ERROR),
                    vec![ERR_CLIENT_ERROR.clone()],
                ));
            };
            program = proj_program;
            source_file = program
                .get_source_file(&params.file.to_file_name())
                .map_or(Node::NIL, |f| f.root);
            if source_file.is_nil() {
                return Err(errors::errorf(
                    format!(
                        "{}: source file not found: {}",
                        *ERR_CLIENT_ERROR,
                        params.file.string()
                    ),
                    vec![ERR_CLIENT_ERROR.clone()],
                ));
            }
            user_preferences = working_snapshot.user_preferences();
        }

        let registry = working_snapshot.auto_import_registry();
        let Some(registry) = registry else {
            return Ok(Some(Vec::new()));
        };

        let (ch, _done) = ls_program::get_type_checker(&program, ctx);

        let view = autoimport::new_view(
            registry,
            source_file,
            project_path,
            program.clone(),
            user_preferences.module_specifier_preferences(),
        );
        let mut import_adder = autoimport::new_import_adder(
            ctx,
            &program,
            source_file,
            Rc::new(view),
            working_snapshot
                .get_preferences(source_file_file_name(source_file))
                .format_code_settings,
            working_snapshot.converters(),
            user_preferences,
        );

        for (i, action) in params.actions.iter().enumerate() {
            match action.kind.0.as_str() {
                IMPORT_ADDER_ACTION_KIND_IMPORT_SYMBOL => {
                    if action.symbol.0 == 0 {
                        return Err(errors::errorf(
                            format!(
                                "{}: import adder action {} missing symbol",
                                *ERR_CLIENT_ERROR, i
                            ),
                            vec![ERR_CLIENT_ERROR.clone()],
                        ));
                    }
                    let (owner, symbol) = sd.resolve_symbol_handle(action.symbol)?;
                    let symbol = checker_symbol(&ch, &owner, symbol);
                    let mut is_valid_type_only_use_site = true;
                    if let Some(value) = action.is_valid_type_only_use_site {
                        is_valid_type_only_use_site = value;
                    }
                    import_adder.add_import_from_exported_symbol(
                        &mut ch.borrow_mut(),
                        symbol,
                        is_valid_type_only_use_site,
                    );
                }
                _ => {
                    return Err(errors::errorf(
                        format!(
                            "{}: unknown import adder action kind {}",
                            *ERR_CLIENT_ERROR,
                            gostd::strconv::quote(&action.kind.0)
                        ),
                        vec![ERR_CLIENT_ERROR.clone()],
                    ));
                }
            }
        }

        if !import_adder.has_fixes() {
            return Ok(Some(Vec::new()));
        }
        Ok(to_api_text_edits(source_file, &import_adder.edits()))
    }
}

// Go: api/session.go:2044 toAPITextEdits (tsgo#3881, tsgo#4712)
// PORT: Go returns nil when an edit position is outside the original text;
// nil is `None`.
pub fn to_api_text_edits(source_file: Node, edits: &[lsproto::TextEdit]) -> Option<Vec<TextEdit>> {
    let original_text = source_file_original_text(source_file);
    let line_map = lsconv::compute_lsp_line_starts(original_text);
    let position_map = compute_position_map(original_text);
    let mut result = Vec::with_capacity(edits.len());
    for edit in edits {
        let (start, ok) = original_text_offset(&line_map, &edit.range.start, original_text.len());
        if !ok {
            return None;
        }
        let (end, ok) = original_text_offset(&line_map, &edit.range.end, original_text.len());
        if !ok {
            return None;
        }
        result.push(TextEdit {
            pos: position_map.utf8_to_utf16(start),
            end: position_map.utf8_to_utf16(end),
            new_text: edit.new_text.clone(),
        });
    }
    Some(result)
}

// Go: api/session.go:2067 originalTextOffset (tsgo#4712)
// PORT: Go `int` arithmetic is `i64` here; the offset is at most the text
// length, so it fits the `i32` that `PositionMap` takes.
pub fn original_text_offset(
    line_map: &lsconv::LSPLineMap,
    position: &lsproto::Position,
    text_length: usize,
) -> (i32, bool) {
    let line = i64::from(position.line);
    if line < 0 || line >= line_map.line_starts.len() as i64 {
        return (0, false);
    }
    let line_start = i64::from(line_map.line_starts[line as usize]);
    let offset = line_start + i64::from(position.character);
    if offset < line_start || offset > text_length as i64 {
        return (0, false);
    }
    (offset as i32, true)
}

// Go: api/session_textedit_test.go (tsgo#4712)
#[cfg(test)]
mod textedit_tests {
    use super::*;
    use crate::frontend::parser::{self, SourceFileParseOptions};

    // Go: api/session_textedit_test.go:14 TestToAPITextEditsUsesOriginalCoordinates
    // PORT: Go sets the info on the parsed `*ast.SourceFile`. Here the parse
    // is recorded (`program::note_parsed_source_file`) and the info is set on
    // the `ParsedSourceFile`, as the content mapper transform does.
    #[test]
    fn test_to_api_text_edits_uses_original_coordinates() {
        let source_file = Rc::new(parser::parse_source_file(
            &SourceFileParseOptions {
                file_name: "/app.vue".to_string(),
                path: tspath::Path("/app.vue".to_string()),
                ..Default::default()
            },
            "const transformed = true;",
            ScriptKind::TS,
        ));
        crate::program::note_parsed_source_file(&source_file);
        source_file.set_content_mapper_info(ContentMapperSourceFileInfo {
            original_text: "😀\nabc".to_string(),
            content_mapper: "mapper".to_string(),
            ..Default::default()
        });

        let edits = to_api_text_edits(
            source_file.root,
            &[lsproto::TextEdit {
                range: lsproto::Range {
                    start: lsproto::Position {
                        line: 1,
                        character: 1,
                    },
                    end: lsproto::Position {
                        line: 1,
                        character: 2,
                    },
                },
                new_text: "x".to_string(),
            }],
        );

        assert_eq!(
            edits,
            Some(vec![TextEdit {
                pos: 4,
                end: 5,
                new_text: "x".to_string(),
            }])
        );
    }
}
