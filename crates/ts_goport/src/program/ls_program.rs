//! Go `*compiler.Program` checker and diagnostics methods for the language
//! service, plus the Go compiler checker pool (`compiler/checkerpool.go`).
//!
//! Everything here runs on the LSP dispatch thread. Go `*compiler.Program`
//! is `&'static NewProgram`. A Go program method `p.X(..)` that the
//! language service needs is `ls_program::x(p, ..)`.
//!
//! Programs: each `NewProgram` made by `new_program` or `update_program` is
//! also a program version of the process (`program::new_program_version`),
//! as Go makes a new `Program` for each snapshot change. Versions share the
//! file versions they have in common. The checkers of every version are
//! made here, on the dispatch thread.
//!
//! Current program: the checker and the `program.rs` functions that it
//! calls read `prog()`. `enter` makes a program current while a
//! `ProgramGuard` lives. A language service holds a guard for its program,
//! a checker from `get_type_checker*` holds one until its release, and the
//! functions here enter the program they are given. Guards can drop in any
//! order: the current program is the one of the last guard that is still
//! alive.
//!
//! Release: Go frees a program when no snapshot and no request uses it.
//! `release_program` is the snapshot part (Go `programCounter.Deref`); the
//! release waits until no guard of the program is alive. The program shell
//! and its file versions stay leaked (see `program::release_program`).
//!
//! PORT: Go keeps the checker pools in `Program` fields. `NewProgram` does
//! not have them, so they live in a thread-local registry keyed by the
//! program address (`ProgramCheckers`).
//!
//! The compile path (`program::with_type_checker_for_file`, the worker
//! pool) is separate and does not change.

use super::*;
use crate::frontend::compiler::{CompilerHost, NewProgram, ProgramOptions};
use crate::frontend::parser::ParsedSourceFile;
use crate::frontend::tspath;
use crate::gostd::Context;
use std::cell::{Cell, OnceCell};

// ---------------------------------------------------------------------------
// Release, CheckerPool
// ---------------------------------------------------------------------------

/// Go `func()` that releases a checker (the `done` of
/// `GetTypeCheckerForFile`). It runs once: on `call` or on drop, whichever
/// comes first.
// PORT: Go wraps release functions in `sync.OnceFunc`.
pub struct Release(Option<Box<dyn FnOnce()>>);

impl Release {
    pub fn new(f: impl FnOnce() + 'static) -> Release {
        Release(Some(Box::new(f)))
    }

    // Go: compiler/checkerpool.go:167 noop
    pub fn noop() -> Release {
        Release(None)
    }

    pub fn call(mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

impl Drop for Release {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

// Go: compiler/checkerpool.go:20 CheckerPool
// CheckerPool is implemented by the project system to provide checkers with
// request-scoped lifetime and reclamation. It returns a checker and a release
// function that must be called when the caller is done with the checker.
// The returned checker must not be accessed concurrently; each acquisition is exclusive.
// If file is non-nil, the pool may use it as an affinity hint to return the same
// checker for the same file across calls.
// PORT: `file` is `Node::NIL` for Go nil. The caller borrows the checker
// (`borrow_mut`) while it uses it.
pub trait CheckerPool {
    fn get_checker(&self, ctx: &Context, file: Node) -> (Rc<RefCell<Checker>>, Release);
}

/// Go `ProgramOptions.CreateCheckerPool`.
pub type CreateCheckerPool = Rc<dyn Fn(&'static NewProgram) -> Rc<dyn CheckerPool>>;

// ---------------------------------------------------------------------------
// Program registry
// ---------------------------------------------------------------------------

/// The Go `Program` fields that `NewProgram` does not hold.
struct ProgramCheckers {
    /// The frontend program.
    program: &'static NewProgram,
    /// Its program version.
    version: &'static GoProgram,
    /// Go `Program.opts.CreateCheckerPool`.
    create_checker_pool: Option<CreateCheckerPool>,
    /// Go `Program.checkerPool`.
    checker_pool: Rc<dyn CheckerPool>,
    /// Go `Program.compilerCheckerPool`.
    compiler_checker_pool: Option<Rc<CompilerCheckerPool>>,
    /// Go `Program.declarationDiagnosticCache`.
    declaration_diagnostic_cache: RefCell<FxHashMap<Node, Vec<Diagnostic>>>,
}

thread_local! {
    // Go: checker/checker.go:577 nextCheckerID
    // PORT: every language-service checker is made on the dispatch thread,
    // so the Go atomic is a thread-local counter.
    static NEXT_CHECKER_ID: Cell<u32> = const { Cell::new(0) };

    /// The checker pools of each program made by `new_program` or
    /// `update_program`, by program address. `release_program` removes an
    /// entry.
    static PROGRAM_CHECKERS: RefCell<FxHashMap<usize, Rc<ProgramCheckers>>> =
        RefCell::new(FxHashMap::default());

    /// The live guards of this thread, oldest first: the guard token and
    /// its program version.
    static GUARDS: RefCell<Vec<(u64, &'static GoProgram)>> = const { RefCell::new(Vec::new()) };

    /// The token of the next guard.
    static NEXT_GUARD: Cell<u64> = const { Cell::new(0) };

    /// The current program of this thread before its first live guard; it
    /// is current again when the last guard drops.
    static BEFORE_GUARDS: Cell<Option<&'static GoProgram>> = const { Cell::new(None) };

    /// Programs that `release_program` released while a guard of theirs was
    /// alive, by program version id. The last such guard releases them.
    static RELEASE_PENDING: RefCell<FxHashMap<u32, &'static NewProgram>> =
        RefCell::new(FxHashMap::default());
}

/// Registry key of `p`.
fn program_key(p: &'static NewProgram) -> usize {
    p as *const NewProgram as usize
}

/// The registry entry of `p`. Panics for a program that `new_program` or
/// `update_program` did not make, or that is released.
fn program_checkers(p: &'static NewProgram) -> Rc<ProgramCheckers> {
    PROGRAM_CHECKERS
        .with(|programs| programs.borrow().get(&program_key(p)).cloned())
        .expect("program was not made by ls_program::new_program, or it is released")
}

/// The program version of `p`.
pub fn program_version(p: &'static NewProgram) -> &'static GoProgram {
    program_checkers(p).version
}

/// The parsed file whose root is `file`, from any program made here that
/// is not released, or None. Go `*ast.SourceFile` is one object in every
/// program that has it; here the programs hold the `ParsedSourceFile`.
/// A file that is not published yet (Go `parser.ParseSourceFile` outside a
/// program) has the parse that `program::note_parsed_source_file` recorded
/// on this thread.
pub fn parsed_source_file(file: Node) -> Option<Rc<ParsedSourceFile>> {
    let Some(go_file) = crate::ast::try_go_file(file.file_index()) else {
        return super::go_frontend::unpublished_parsed_source_file(file.file_index())
            .filter(|parsed| parsed.root == file);
    };
    let path = tspath::Path(go_file.info.path.clone());
    let programs: Vec<&'static NewProgram> = PROGRAM_CHECKERS.with(|programs| {
        programs
            .borrow()
            .values()
            .map(|checkers| checkers.program)
            .collect()
    });
    programs.into_iter().find_map(|p| {
        p.get_source_file_by_path(&path)
            .filter(|parsed| parsed.root == file)
    })
}

// ---------------------------------------------------------------------------
// Current program
// ---------------------------------------------------------------------------

/// From `enter`: `p` is current on this thread while the guard lives, unless
/// a later guard that is still alive made another program current. It is
/// `!Send`, so it drops on the thread that made it.
#[must_use = "the program is current only while the guard lives"]
pub struct ProgramGuard {
    token: u64,
    version: &'static GoProgram,
    _not_send: std::marker::PhantomData<*const ()>,
}

/// Makes `p` the current program of this thread while the guard lives.
pub fn enter(p: &'static NewProgram) -> ProgramGuard {
    enter_version(program_version(p))
}

/// `enter` for a program version. Use it for a version that no `NewProgram`
/// makes (`program::new_alias_resolver_program`).
pub fn enter_version(version: &'static GoProgram) -> ProgramGuard {
    let token = NEXT_GUARD.with(|next| {
        let token = next.get();
        next.set(token + 1);
        token
    });
    GUARDS.with(|guards| {
        let mut guards = guards.borrow_mut();
        if guards.is_empty() {
            BEFORE_GUARDS.with(|before| before.set(try_prog()));
        }
        guards.push((token, version));
    });
    crate::core::set_thread_program(Some(version));
    ProgramGuard {
        token,
        version,
        _not_send: std::marker::PhantomData,
    }
}

impl ProgramGuard {
    /// A `Release` that drops this guard after `release` runs: the checker
    /// that `release` gives back runs with the program current until then.
    pub fn with_release(self, release: Release) -> Release {
        Release::new(move || {
            release.call();
            drop(self);
        })
    }
}

impl Drop for ProgramGuard {
    fn drop(&mut self) {
        let (current, still_entered) = GUARDS.with(|guards| {
            let mut guards = guards.borrow_mut();
            if let Some(i) = guards.iter().position(|&(token, _)| token == self.token) {
                guards.remove(i);
            }
            let current = match guards.last() {
                Some(&(_, version)) => Some(version),
                None => BEFORE_GUARDS.with(Cell::get),
            };
            let still_entered = guards
                .iter()
                .any(|&(_, version)| std::ptr::eq(version, self.version));
            (current, still_entered)
        });
        crate::core::set_thread_program(current);
        if !still_entered {
            let pending =
                RELEASE_PENDING.with(|pending| pending.borrow_mut().remove(&self.version.id));
            if let Some(p) = pending {
                release_now(p);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Program construction and release
// ---------------------------------------------------------------------------

// Go: compiler/program.go:269 NewProgram
// PORT: Go `opts.CreateCheckerPool` is the `create_checker_pool` argument.
// The frontend program parses with no current program, then becomes a
// program version of the process (`program::new_program_version`).
// PORT: Go runs `initCheckerPool` before `verifyCompilerOptions`. Here the
// pool is set up after the program is built. Neither step reads the other.
pub fn new_program(
    opts: ProgramOptions,
    create_checker_pool: Option<CreateCheckerPool>,
) -> &'static NewProgram {
    let p: &'static NewProgram = {
        let _scope = crate::core::enter_program(None);
        Box::leak(Box::new(crate::frontend::compiler::new_program(opts)))
    };
    let version = new_program_version(p, None);
    init_checker_pool(p, version, create_checker_pool);
    p
}

// Go: compiler/program.go:288 UpdateProgram
// PORT: `NewProgram::update_program` builds the new program. It is leaked,
// becomes a program version that shares the unchanged file versions of
// `p`, and gets its checker pool here. `create_checker_pool`, when set,
// overrides the one of `p` (Go `newOpts.CreateCheckerPool`).
pub fn update_program(
    p: &'static NewProgram,
    changed_file_path: &tspath::Path,
    new_host: Rc<dyn CompilerHost>,
    create_checker_pool: Option<CreateCheckerPool>,
) -> (&'static NewProgram, Option<Rc<ParsedSourceFile>>, bool) {
    let old = PROGRAM_CHECKERS.with(|programs| programs.borrow().get(&program_key(p)).cloned());
    let create_checker_pool = create_checker_pool.or_else(|| {
        old.as_ref()
            .expect("program was not made by ls_program::new_program, or it is released")
            .create_checker_pool
            .clone()
    });
    let (result, new_file, reused) = {
        let _scope = crate::core::enter_program(None);
        p.update_program(changed_file_path, new_host)
    };
    let result: &'static NewProgram = Box::leak(Box::new(result));
    let version = new_program_version(result, old.map(|old| old.version));
    init_checker_pool(result, version, create_checker_pool);
    (result, new_file, reused)
}

/// Go drops a program when no snapshot uses it (`programCounter.Deref`
/// returns true) and no request holds it. This is the snapshot part: the
/// checker pools of `p` and its program version are freed now, or when the
/// last guard of `p` drops (a request that still runs on it).
pub fn release_program(p: &'static NewProgram) {
    let Some(checkers) =
        PROGRAM_CHECKERS.with(|programs| programs.borrow().get(&program_key(p)).cloned())
    else {
        return;
    };
    let entered = GUARDS.with(|guards| {
        guards
            .borrow()
            .iter()
            .any(|&(_, version)| std::ptr::eq(version, checkers.version))
    });
    if entered {
        RELEASE_PENDING.with(|pending| pending.borrow_mut().insert(checkers.version.id, p));
    } else {
        release_now(p);
    }
}

/// Removes `p` from the registry, which drops its checker pools once no
/// project holds them, and releases its program version.
fn release_now(p: &'static NewProgram) {
    let Some(checkers) =
        PROGRAM_CHECKERS.with(|programs| programs.borrow_mut().remove(&program_key(p)))
    else {
        return;
    };
    crate::program::release_program(checkers.version);
}

// Go: compiler/program.go:335 initCheckerPool
fn init_checker_pool(
    p: &'static NewProgram,
    version: &'static GoProgram,
    create_checker_pool: Option<CreateCheckerPool>,
) {
    if !p.finished_processing {
        panic!("Program must finish processing files before initializing checker pool");
    }

    let (checker_pool, compiler_checker_pool): (
        Rc<dyn CheckerPool>,
        Option<Rc<CompilerCheckerPool>>,
    ) = if let Some(create) = &create_checker_pool {
        (create(p), None)
    } else {
        let pool = Rc::new(new_checker_pool_with_tracing(p));
        let checker_pool: Rc<dyn CheckerPool> = pool.clone();
        (checker_pool, Some(pool))
    };
    let checkers = Rc::new(ProgramCheckers {
        program: p,
        version,
        create_checker_pool,
        checker_pool,
        compiler_checker_pool,
        declaration_diagnostic_cache: RefCell::new(FxHashMap::default()),
    });
    PROGRAM_CHECKERS.with(|programs| {
        programs.borrow_mut().insert(program_key(p), checkers);
    });
}

// Go: compiler/program.go:350 GetCheckerPool
// GetCheckerPool returns the checker pool associated with this program.
pub fn get_checker_pool(p: &'static NewProgram) -> Rc<dyn CheckerPool> {
    program_checkers(p).checker_pool.clone()
}

// Go: checker/checker.go:900 NewChecker (the checker id)
// PORT: Go `NewChecker(program, tracer)` also returns the checker mutex; a
// pool here holds `Rc<RefCell<Checker>>` and the borrow is the lock. The
// tracer is dropped. Go `program.BindSourceFiles()` runs inside
// `Checker::new` (`bind_all`), with the program of `p` current.
// PORT: Go `c.id = nextCheckerID.Add(1)`. `Checker::new(index)` sets
// `id = index + 1`, so the index is the counter value before the add.
pub fn new_checker(p: &'static NewProgram) -> Checker {
    new_checker_for_version(program_version(p))
}

/// `new_checker` for a program version. Go `checker.NewChecker(program)`
/// takes any `checker.Program`; the autoimport alias resolver's program
/// (`program::new_alias_resolver_program`) has no `NewProgram`.
pub fn new_checker_for_version(version: &'static GoProgram) -> Checker {
    let _program = enter_version(version);
    let id = NEXT_CHECKER_ID.with(|next| {
        let id = next.get() + 1;
        next.set(id);
        id
    });
    Checker::new((id - 1) as usize)
}

// ---------------------------------------------------------------------------
// Compiler checker pool (Go compiler/checkerpool.go)
// ---------------------------------------------------------------------------

// Go: compiler/checkerpool.go:24 checkerPool
// PORT: the pool lives on the dispatch thread. Go `locks` are the
// `RefCell` of each checker: a caller holds `borrow_mut` where Go holds the
// lock, and a second borrow panics where Go would block. `tracing` is dropped.
// PORT: Go `checkers` starts as a list of nil pointers; each slot here is
// an empty `OnceCell` until `createCheckers`. Go `fileAssociations` maps a
// file to its checker; here it maps the file index to the checker index.
pub struct CompilerCheckerPool {
    program: &'static NewProgram,
    create_checkers_once: Cell<bool>,
    checkers: Vec<OnceCell<Rc<RefCell<Checker>>>>,
    file_associations: OnceCell<FxHashMap<usize, usize>>,
}

// Go: compiler/checkerpool.go:36 newCheckerPool
fn new_checker_pool(program: &'static NewProgram) -> CompilerCheckerPool {
    new_checker_pool_with_tracing(program)
}

// Go: compiler/checkerpool.go:40 newCheckerPoolWithTracing
// PORT: tracing is dropped.
fn new_checker_pool_with_tracing(program: &'static NewProgram) -> CompilerCheckerPool {
    let mut checker_count: i64 = 4;
    if program.single_threaded() {
        checker_count = 1;
    } else if let Some(c) = program.options().checkers {
        checker_count = i64::from(c);
    }

    checker_count = checker_count
        .min(program.files.len() as i64)
        .min(256)
        .max(1);

    CompilerCheckerPool {
        program,
        create_checkers_once: Cell::new(false),
        checkers: (0..checker_count).map(|_| OnceCell::new()).collect(),
        file_associations: OnceCell::new(),
    }
}

impl CheckerPool for CompilerCheckerPool {
    // Go: compiler/checkerpool.go:62 (*checkerPool).GetChecker
    // GetChecker implements CheckerPool. When file is non-nil, returns the checker
    // associated with that file; otherwise returns the first checker.
    // PORT: Go locks checker 0 and returns the unlock. The lock is the
    // caller's borrow, so the release does nothing.
    fn get_checker(&self, ctx: &Context, file: Node) -> (Rc<RefCell<Checker>>, Release) {
        if file.is_some() {
            return self.get_checker_for_file_exclusive(ctx, file);
        }
        self.create_checkers();
        let c = Rc::clone(self.checker(0));
        (c, Release::noop())
    }
}

impl CompilerCheckerPool {
    /// Go `p.checkers[i]` after `createCheckers`.
    fn checker(&self, i: usize) -> &Rc<RefCell<Checker>> {
        self.checkers[i]
            .get()
            .expect("checkers are made by createCheckers")
    }

    /// The checker index of `file` (Go `fileAssociations[file]`).
    // PORT: Go returns a nil checker for a file outside the program, and
    // its callers then fail on it. This panics.
    fn checker_index_for_file(&self, file: Node) -> usize {
        *self
            .file_associations
            .get()
            .expect("checkers are made by createCheckers")
            .get(&file.file_index())
            .expect("file is not in the program")
    }

    // Go: compiler/checkerpool.go:77 (*checkerPool).getCheckerForFileNonExclusive
    // getCheckerForFileNonExclusive returns the checker for the given file without locking.
    // This is only safe when the caller guarantees no concurrent access to the same checker,
    // e.g. for read-only operations like obtaining an emit resolver.
    fn get_checker_for_file_non_exclusive(&self, file: Node) -> (Rc<RefCell<Checker>>, Release) {
        self.create_checkers();
        let c = Rc::clone(self.checker(self.checker_index_for_file(file)));
        (c, Release::noop())
    }

    // Go: compiler/checkerpool.go:82 (*checkerPool).getCheckerForFileExclusive
    // PORT: Go locks the checker and returns the unlock. The lock is the
    // caller's borrow, so the release does nothing.
    fn get_checker_for_file_exclusive(
        &self,
        ctx: &Context,
        file: Node,
    ) -> (Rc<RefCell<Checker>>, Release) {
        self.create_checkers();
        let idx = self.checker_index_for_file(file);
        let c = Rc::clone(self.checker(idx));
        (c, Release::noop())
    }

    // Go: compiler/checkerpool.go:93 (*checkerPool).getCheckerNonExclusive
    // getCheckerNonExclusive returns the first checker without locking.
    fn get_checker_non_exclusive(&self) -> (Rc<RefCell<Checker>>, Release) {
        self.create_checkers();
        (Rc::clone(self.checker(0)), Release::noop())
    }

    // Go: compiler/checkerpool.go:98 (*checkerPool).createCheckers
    // PORT: Go `createCheckersOnce` is a flag. Go makes the checkers on a
    // WorkGroup; here they are made in index order, so their ids follow the
    // index.
    fn create_checkers(&self) {
        if self.create_checkers_once.replace(true) {
            return;
        }
        let checker_count = self.checkers.len();
        for i in 0..checker_count {
            let checker = new_checker(self.program);
            let _ = self.checkers[i].set(Rc::new(RefCell::new(checker)));
        }

        let mut file_associations = FxHashMap::default();
        for (i, file) in self.program.files.iter().enumerate() {
            file_associations.insert(file.root.file_index(), i % checker_count);
        }
        let _ = self.file_associations.set(file_associations);
    }

    // Go: compiler/checkerpool.go:123 (*checkerPool).forEachCheckerParallel
    // Runs `cb` for each checker in the pool concurrently, locking and unlocking checker mutexes as it goes,
    // making it safe to call `forEachCheckerParallel` from many threads simultaneously.
    // PORT: on the dispatch thread the checkers run one after another, in
    // index order.
    pub fn for_each_checker_parallel(&self, cb: &mut dyn FnMut(usize, &mut Checker)) {
        self.create_checkers();
        for (idx, checker) in self.checkers.iter().enumerate() {
            let checker = checker.get().expect("checkers are made by createCheckers");
            cb(idx, &mut checker.borrow_mut());
        }
    }

    // Go: compiler/checkerpool.go:136 (*checkerPool).GetGlobalDiagnostics
    pub fn get_global_diagnostics(&self) -> Vec<Diagnostic> {
        self.create_checkers();
        let mut global_diagnostics: Vec<Vec<Diagnostic>> = vec![Vec::new(); self.checkers.len()];
        self.for_each_checker_parallel(&mut |idx, checker| {
            global_diagnostics[idx] = checker.get_global_diagnostics();
        });
        sort_and_deduplicate_diagnostics(global_diagnostics.into_iter().flatten().collect())
    }

    // Go: compiler/checkerpool.go:148 (*checkerPool).forEachCheckerGroupDo
    // forEachCheckerGroupDo runs one task per checker in parallel. Each task iterates
    // the provided files, processing only those assigned to its checker. Within each
    // checker's set, files are visited in their original order.
    // PORT: on the dispatch thread the tasks run one after another, in
    // checker order.
    fn for_each_checker_group_do(
        &self,
        ctx: &Context,
        files: &[Node],
        single_threaded: bool,
        cb: &mut dyn FnMut(&mut Checker, usize, Node),
    ) {
        self.create_checkers();

        let checker_count = self.checkers.len();
        let file_associations = self
            .file_associations
            .get()
            .expect("checkers are made by createCheckers");
        for checker_idx in 0..checker_count {
            let mut checker = self.checker(checker_idx).borrow_mut();
            for (i, &file) in files.iter().enumerate() {
                if file_associations.get(&file.file_index()) == Some(&checker_idx) {
                    cb(&mut checker, i, file);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Program checker access (Go compiler/program.go:445-492)
// ---------------------------------------------------------------------------

// Go: compiler/program.go:445 BindSourceFiles
// PORT: the Rust binder binds every file of the program version into one
// arena (`program::bind_all`). A file version that an earlier version
// bound is not bound again.
pub fn bind_source_files(p: &'static NewProgram) {
    let _program = enter(p);
    bind_all();
}

// PORT: each `get_type_checker*` function makes the program of `p` current
// until the returned release runs (see the module comment), so the caller
// uses the checker with its program current.

// Go: compiler/program.go:461 GetTypeChecker
// Return the type checker associated with the program.
pub fn get_type_checker(p: &'static NewProgram, ctx: &Context) -> (Rc<RefCell<Checker>>, Release) {
    let program = enter(p);
    let checkers = program_checkers(p);
    let (checker, release) = match &checkers.compiler_checker_pool {
        Some(pool) => pool.get_checker_non_exclusive(),
        None => checkers.checker_pool.get_checker(ctx, Node::NIL),
    };
    (checker, program.with_release(release))
}

// Go: compiler/program.go:468 ForEachCheckerParallel
pub fn for_each_checker_parallel(p: &'static NewProgram, cb: &mut dyn FnMut(usize, &mut Checker)) {
    let _program = enter(p);
    let checkers = program_checkers(p);
    if let Some(pool) = &checkers.compiler_checker_pool {
        pool.for_each_checker_parallel(cb);
    }
}

// Go: compiler/program.go:478 GetTypeCheckerForFile
// Return a checker for the given file. We may have multiple checkers in concurrent scenarios and this
// method returns the checker that was tasked with checking the file. Note that it isn't possible to mix
// types obtained from different checkers, so only non-type data (such as diagnostics or string
// representations of types) should be obtained from checkers returned by this method.
pub fn get_type_checker_for_file(
    p: &'static NewProgram,
    ctx: &Context,
    file: Node,
) -> (Rc<RefCell<Checker>>, Release) {
    let program = enter(p);
    let checkers = program_checkers(p);
    let (checker, release) = match &checkers.compiler_checker_pool {
        Some(pool) => pool.get_checker_for_file_non_exclusive(file),
        None => checkers.checker_pool.get_checker(ctx, file),
    };
    (checker, program.with_release(release))
}

// Go: compiler/program.go:487 GetTypeCheckerForFileExclusive
// Return a checker for the given file, locked to the current thread to prevent data races from multiple threads
// accessing the same checker. The lock will be released when the `done` function is called.
pub fn get_type_checker_for_file_exclusive(
    p: &'static NewProgram,
    ctx: &Context,
    file: Node,
) -> (Rc<RefCell<Checker>>, Release) {
    let program = enter(p);
    let checkers = program_checkers(p);
    let (checker, release) = match &checkers.compiler_checker_pool {
        Some(pool) => pool.get_checker_for_file_exclusive(ctx, file),
        None => checkers.checker_pool.get_checker(ctx, file),
    };
    (checker, program.with_release(release))
}

// ---------------------------------------------------------------------------
// Diagnostics (Go compiler/program.go:534-712 and 1290-1420)
// ---------------------------------------------------------------------------
//
// PORT: the per-file bodies that already exist in program.rs for the
// current program are called from here: `get_semantic_diagnostics_with_checker`
// (Go program.go:1315 getSemanticDiagnosticsWithChecker),
// `get_bind_and_check_diagnostics_with_checker` (:1325),
// `get_diagnostics_with_preceding_directives` (:1359),
// `get_suggestion_diagnostics_with_checker` (:1410) and
// `get_additional_js_syntactic_diagnostics` (:618). They read the file data
// of the current program; each public function here makes `p` current.

/// Go `p.files` as file nodes.
fn source_file_nodes(p: &'static NewProgram) -> Vec<Node> {
    p.files.iter().map(|file| file.root).collect()
}

// Go: compiler/program.go:534 collectDiagnostics
// collectDiagnostics collects diagnostics from a single file or all files.
// If sourceFile is non-nil, returns diagnostics for just that file.
// If sourceFile is nil, returns diagnostics for all files in the program.
fn collect_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
    concurrent: bool,
    collect: &mut dyn FnMut(&Context, Node) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let result = if source_file.is_some() {
        collect(ctx, source_file)
    } else {
        let diagnostics =
            collect_diagnostics_from_files(p, ctx, &source_file_nodes(p), concurrent, collect);
        diagnostics.into_iter().flatten().collect()
    };
    sort_and_deduplicate_diagnostics(result)
}

// Go: compiler/program.go:545 collectDiagnosticsFromFiles
// PORT: Go runs the files on a WorkGroup. On the dispatch thread they run
// one after another, in file order.
fn collect_diagnostics_from_files(
    p: &'static NewProgram,
    ctx: &Context,
    source_files: &[Node],
    concurrent: bool,
    collect: &mut dyn FnMut(&Context, Node) -> Vec<Diagnostic>,
) -> Vec<Vec<Diagnostic>> {
    let mut diagnostics: Vec<Vec<Diagnostic>> = vec![Vec::new(); source_files.len()];
    for (i, &file) in source_files.iter().enumerate() {
        diagnostics[i] = collect(ctx, file);
    }
    diagnostics
}

// Go: compiler/program.go:562 collectCheckerDiagnostics
// collectCheckerDiagnostics collects diagnostics from a single file or all files,
// using a callback that receives the checker for each file. When the checker pool
// supports grouped iteration (compiler pool), files are grouped by checker and
// processed in parallel with one task per checker, reducing contention and improving
// cache locality. Otherwise, falls back to per-file concurrent collection.
fn collect_checker_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
    collect: &mut dyn FnMut(&Context, &mut Checker, Node) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    if source_file.is_some() {
        if skip_type_checking(p, source_file, false) {
            return Vec::new();
        }
        let (c, done) = get_type_checker_for_file_exclusive(p, ctx, source_file);
        let result = collect(ctx, &mut c.borrow_mut(), source_file);
        done.call();
        return sort_and_deduplicate_diagnostics(result);
    }
    let diagnostics =
        collect_checker_diagnostics_from_files(p, ctx, &source_file_nodes(p), collect);
    sort_and_deduplicate_diagnostics(diagnostics.into_iter().flatten().collect())
}

// Go: compiler/program.go:576 collectCheckerDiagnosticsFromFiles
// collectCheckerDiagnosticsFromFiles collects checker diagnostics for a list of files.
// PORT: Go runs the files of an external pool on a WorkGroup. On the
// dispatch thread they run one after another, in file order.
fn collect_checker_diagnostics_from_files(
    p: &'static NewProgram,
    ctx: &Context,
    source_files: &[Node],
    collect: &mut dyn FnMut(&Context, &mut Checker, Node) -> Vec<Diagnostic>,
) -> Vec<Vec<Diagnostic>> {
    let mut diagnostics: Vec<Vec<Diagnostic>> = vec![Vec::new(); source_files.len()];
    let checkers = program_checkers(p);
    if let Some(pool) = &checkers.compiler_checker_pool {
        pool.for_each_checker_group_do(
            ctx,
            source_files,
            p.single_threaded(),
            &mut |c, file_index, file| {
                diagnostics[file_index] = collect(ctx, c, file);
            },
        );
    } else {
        for (i, &file) in source_files.iter().enumerate() {
            if skip_type_checking(p, file, false) {
                continue;
            }
            let (c, done) = checkers.checker_pool.get_checker(ctx, file);
            diagnostics[i] = collect(ctx, &mut c.borrow_mut(), file);
            done.call();
        }
    }
    diagnostics
}

// Go: compiler/program.go:599 GetSyntacticDiagnostics
pub fn get_syntactic_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    let options = p.options();
    collect_diagnostics(
        p,
        ctx,
        source_file,
        false, /*concurrent*/
        &mut |_ctx, file| {
            let info = source_file_info(file);
            let mut diags: Vec<Diagnostic> = info
                .diagnostics
                .iter()
                .chain(&info.js_diagnostics)
                .cloned()
                .collect();
            // For JS files that won't be checked by the checker (no checkJs/ts-check), we need
            // program-level syntactic checks that require compiler options. This mirrors Strada's
            // getJSSyntacticDiagnosticsForFile in program.ts.
            if is_source_file_js(file) && !is_check_js_enabled_for_file(file, options) {
                diags.extend(get_additional_js_syntactic_diagnostics(file, options));
            }
            diags
        },
    )
}

// Go: compiler/program.go:643 GetBindDiagnostics
// PORT: Go binds only `sourceFile` when it is set, else every file. The
// Rust binder binds every file of the program version into one arena, so
// both cases bind all files.
pub fn get_bind_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    bind_source_files(p);
    collect_diagnostics(
        p,
        ctx,
        source_file,
        false, /*concurrent*/
        &mut |_ctx, file| file_bind_data(file).bind_diagnostics.clone(),
    )
}

// Go: compiler/program.go:654 GetSemanticDiagnostics
pub fn get_semantic_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    collect_checker_diagnostics(p, ctx, source_file, &mut |_ctx, c, file| {
        get_semantic_diagnostics_with_checker(c, file)
    })
}

// Go: compiler/program.go:658 GetSemanticDiagnosticsWithoutNoEmitFiltering
pub fn get_semantic_diagnostics_without_no_emit_filtering(
    p: &'static NewProgram,
    ctx: &Context,
    source_files: &[Node],
) -> FxHashMap<Node, Vec<Diagnostic>> {
    let _program = enter(p);
    let all_diags =
        collect_checker_diagnostics_from_files(p, ctx, source_files, &mut |_ctx, c, file| {
            get_bind_and_check_diagnostics_with_checker(c, file)
        });
    let mut result = FxHashMap::default();
    for (i, diags) in all_diags.into_iter().enumerate() {
        result.insert(source_files[i], sort_and_deduplicate_diagnostics(diags));
    }
    result
}

// Go: compiler/program.go:667 GetSuggestionDiagnostics
pub fn get_suggestion_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    collect_checker_diagnostics(p, ctx, source_file, &mut |_ctx, c, file| {
        get_suggestion_diagnostics_with_checker(c, file)
    })
}

// Go: compiler/program.go:671 GetProgramDiagnostics
pub fn get_program_diagnostics(p: &'static NewProgram) -> Vec<Diagnostic> {
    let _program = enter(p);
    let mut diagnostics = p.program_diagnostics.clone();
    diagnostics.extend(
        p.include_processor
            .get_diagnostics(p)
            .borrow_mut()
            .get_global_diagnostics(),
    );
    sort_and_deduplicate_diagnostics(diagnostics)
}

// Go: compiler/program.go:678 GetIncludeProcessorDiagnostics
pub fn get_include_processor_diagnostics(
    p: &'static NewProgram,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    if skip_type_checking(p, source_file, false) {
        return Vec::new();
    }
    let diagnostics = p
        .include_processor
        .get_diagnostics(p)
        .borrow_mut()
        .get_diagnostics_for_file(source_file_file_name(source_file));
    let (filtered, _) = get_diagnostics_with_preceding_directives(source_file, diagnostics);
    filtered
}

// Go: compiler/program.go:686 SkipTypeChecking
pub fn skip_type_checking(
    p: &'static NewProgram,
    source_file: Node,
    ignore_no_check: bool,
) -> bool {
    let _program = enter(p);
    let options = p.options();
    let info = source_file_info(source_file);
    let path = tspath::Path(info.path.clone());
    (!ignore_no_check && options.no_check.is_true())
        || options.skip_lib_check.is_true() && info.is_declaration_file
        || options.skip_default_lib_check.is_true() && p.is_source_file_default_library(&path)
        || p.is_source_from_project_reference(&path)
        || !can_include_bind_and_check_diagnostics(p, source_file)
}

// Go: compiler/program.go:694 canIncludeBindAndCheckDiagnostics
fn can_include_bind_and_check_diagnostics(p: &'static NewProgram, source_file: Node) -> bool {
    let info = source_file_info(source_file);
    if info.check_js_directive.is_some_and(|d| !d.enabled) {
        return false;
    }

    if info.script_kind == ScriptKind::TS
        || info.script_kind == ScriptKind::TSX
        || info.script_kind == ScriptKind::EXTERNAL
    {
        return true;
    }

    let is_js = info.script_kind == ScriptKind::JS || info.script_kind == ScriptKind::JSX;
    let is_check_js = is_js && is_check_js_enabled_for_file(source_file, p.options());
    let is_plain_js = is_plain_js_file(source_file, p.options().check_js);

    // By default, only type-check .ts, .tsx, Deferred, plain JS, checked JS and External
    // - plain JS: .js files with no // ts-check and checkJs: undefined
    // - check JS: .js files with either // ts-check or checkJs: true
    // - external: files that are added by plugins
    is_plain_js || is_check_js || info.script_kind == ScriptKind::DEFERRED
}

// Go: compiler/program.go:1290 GetGlobalDiagnostics
pub fn get_global_diagnostics(p: &'static NewProgram, ctx: &Context) -> Vec<Diagnostic> {
    let _program = enter(p);
    if p.files.is_empty() {
        return Vec::new();
    }
    let checkers = program_checkers(p);
    if let Some(pool) = &checkers.compiler_checker_pool {
        return pool.get_global_diagnostics();
    }
    // For external pools (project system), global diagnostics are collected
    // incrementally as checkers are used, not via a bulk query.
    Vec::new()
}

// Go: compiler/program.go:1302 GetDeclarationDiagnostics
pub fn get_declaration_diagnostics(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    let _program = enter(p);
    collect_diagnostics(
        p,
        ctx,
        source_file,
        true, /*concurrent*/
        &mut |ctx, file| get_declaration_diagnostics_for_file(p, ctx, file),
    )
}

// Go: compiler/program.go:1394 getDeclarationDiagnosticsForFile
fn get_declaration_diagnostics_for_file(
    p: &'static NewProgram,
    ctx: &Context,
    source_file: Node,
) -> Vec<Diagnostic> {
    if source_file_info(source_file).is_declaration_file {
        return Vec::new();
    }

    let checkers = program_checkers(p);
    if let Some(cached) = checkers
        .declaration_diagnostic_cache
        .borrow()
        .get(&source_file)
    {
        return cached.clone();
    }

    let (host, done) = new_emit_host(p, ctx, source_file);
    let diagnostics = get_declaration_diagnostics_worker(host, source_file);
    // Go `LoadOrStore`: keep the first stored value.
    let diagnostics = checkers
        .declaration_diagnostic_cache
        .borrow_mut()
        .entry(source_file)
        .or_insert(diagnostics)
        .clone();
    // Go `defer done()`.
    done.call();
    diagnostics
}

// Go: compiler/emitHost.go:38 newEmitHost
// PORT: the language-service form of `program::new_emit_host`. The checker
// comes from `GetTypeCheckerForFile` of `p`, which a dispatch-thread pool
// shares as `Rc<RefCell<Checker>>`, so the resolver links to that `Rc`
// (`get_emit_resolver_of_shared_checker`) instead of a compile worker
// checker. The host methods read the current program, which is `p`.
// `EmitHost.checker_index` is the resolver's index; only the compile path
// (JS emit on a worker thread) uses it.
fn new_emit_host(p: &'static NewProgram, ctx: &Context, file: Node) -> (Rc<EmitHost>, Release) {
    let (checker, done) = get_type_checker_for_file(p, ctx, file);
    let emit_resolver =
        crate::checker::emit_resolver_p1::get_emit_resolver_of_shared_checker(&checker);
    let host = Rc::new(EmitHost {
        checker_index: emit_resolver.checker_index,
        emit_resolver,
    });
    (host, done)
}

// Go: compiler/program.go:1548 IsGlobalTypingsFile
pub fn is_global_typings_file(p: &'static NewProgram, file_name: &str) -> bool {
    if !tspath::is_declaration_file_name(file_name) {
        return false;
    }
    tspath::contains_path(
        &p.get_global_typings_cache_location(),
        file_name,
        &p.compare_paths_options,
    )
}
