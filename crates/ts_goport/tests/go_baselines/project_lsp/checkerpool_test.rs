//! Port of Go `internal/project/checkerpool_test.go`.
//!
//! PORT: the Rust pool lives on one thread (see `project::checkerpool`):
//! a second request for a full slot is `unreachable!` there, so the Go
//! contention tests (`QueryContention`, `DiagnosticsContention`, the 4th
//! request of `MultipleConcurrentQueryCheckers`) are not ported. Go runs
//! the timer tests in `synctest` bubbles; the idle-cleanup timer here is a
//! `gostd::local` timer that only fires in `run_pending`, so the tests
//! that wait for it (`IdleCleanup`, `FileAssociationCleanup`,
//! `StaggeredIdleCleanup`, `RequestAssociationCleanupOnContextDone`,
//! `DiagnosticsRecreatedAfterIdleDisposal`, `CrossReleaseAffinityWithContention`)
//! are not ported, and the long fake sleeps of the other tests are left
//! out. `DoubleReleaseSafe` can not be written: `Release::call` takes
//! `self`. Go `synctest.Wait()` has nothing to wait for on one thread.

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use ts_goport::checker::Checker;
use ts_goport::frontend::bundled;
use ts_goport::frontend::core_context::{self, CheckerLifetime};
use ts_goport::gostd::{Context, context};
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program::CheckerPool as _;
use ts_goport::project::{
    self, CheckerPool, CheckerPoolOptions, Session, logging, new_checker_pool,
};

use super::projecttestutil::{self, files};
use super::util::*;

type CheckerRc = Rc<RefCell<Checker>>;

fn opts(max_checkers: i32, idle_secs: u64) -> CheckerPoolOptions {
    CheckerPoolOptions {
        max_checkers,
        idle_timeout: Duration::from_secs(idle_secs),
    }
}

// Go: checkerpool_test.go:20 setupCheckerPoolSession
fn setup_checker_pool_session(opts: CheckerPoolOptions) -> (Rc<Session>, Rc<CheckerPool>) {
    let (_, fs) = projecttestutil::wrapped_map_fs(
        files(&[
            (
                "/src/tsconfig.json",
                r#"{ "compilerOptions": { "noLib": true } }"#,
            ),
            ("/src/index.ts", "export const x: number = 1;"),
        ]),
        false,
    );
    let logger: Rc<dyn logging::Logger> = logging::new_test_logger();
    let session = project::new_session(&project::SessionInit {
        background_ctx: bg(),
        options: Rc::new(project::SessionOptions {
            current_directory: "/".to_string(),
            default_library_path: bundled::lib_path(),
            typings_location: String::new(),
            position_encoding: lsproto::PositionEncodingKind::UTF8,
            watch_enabled: false,
            logging_enabled: true,
            checker_pool_options: opts,
            ..projecttestutil::session_options("/")
        }),
        fs,
        client: None,
        logger: Some(logger),
        npm_executor: None,
        parse_cache: None,
    });
    open(
        &session,
        "file:///src/index.ts",
        "export const x: number = 1;",
    );

    let project =
        configured_project(&session, "/src/tsconfig.json").expect("expected configured project");
    let pool = project
        .borrow()
        .checker_pool
        .clone()
        .expect("expected checker pool");
    (session, pool)
}

// Go: checkerpool_test.go:55 newTestCheckerPool
fn new_test_checker_pool(
    program: &'static ts_goport::frontend::compiler::NewProgram,
    opts: CheckerPoolOptions,
) -> Rc<CheckerPool> {
    new_checker_pool(opts, program, Some(Rc::new(|_: &str| {})))
}

/// The session's program and a fresh test pool on it (the start of most Go tests).
fn test_pool(
    session_opts: CheckerPoolOptions,
    pool_opts: CheckerPoolOptions,
) -> (Rc<Session>, Rc<CheckerPool>) {
    let (session, _) = setup_checker_pool_session(session_opts);
    let p = program(&session, "file:///src/index.ts");
    let pool = new_test_checker_pool(p, pool_opts);
    (session, pool)
}

/// Go `core.WithCheckerLifetime(core.WithRequestID(parent, id), lifetime)`.
fn req(parent: &Context, id: &str, lifetime: CheckerLifetime) -> Context {
    core_context::with_checker_lifetime(&core_context::with_request_id(parent, id), lifetime)
}

fn checker_at(pool: &CheckerPool, index: usize) -> Option<CheckerRc> {
    pool.checkers.borrow()[index].clone()
}

fn same(a: &CheckerRc, b: &CheckerRc) -> bool {
    Rc::ptr_eq(a, b)
}

/// The query slot (1+) that holds `c`, or 0.
fn query_index(pool: &CheckerPool, c: &CheckerRc) -> usize {
    let checkers = pool.checkers.borrow();
    (1..checkers.len())
        .find(|&i| checkers[i].as_ref().is_some_and(|x| same(x, c)))
        .unwrap_or(0)
}

const NIL: ts_goport::core::Node = ts_goport::core::Node::NIL;

child_test! {
    // Go: checkerpool_test.go:59 TestCheckerPoolDiagnosticsRouting
    fn diagnostics_routing() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));

        // Diagnostics requests should get checker at index 0.
        let ctx = req(&bg(), "diag-req-1", CheckerLifetime::DIAGNOSTICS);
        let (c, release) = pool.get_checker(&ctx, NIL);
        assert!(checker_at(&pool, 0).is_some_and(|x| same(&x, &c)), "diagnostics should use checker index 0");
        release.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:72 TestCheckerPoolQueryRouting
    fn query_routing() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));

        // Query requests should get a checker at index > 0.
        let ctx = req(&bg(), "query-req-1", CheckerLifetime::TEMPORARY);
        let (c, release) = pool.get_checker(&ctx, NIL);

        // Verify it's not the diagnostics checker slot.
        assert!(
            !checker_at(&pool, 0).is_some_and(|x| same(&x, &c)),
            "query should not use checker index 0"
        );
        release.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:87 TestCheckerPoolRequestAffinity
    fn request_affinity() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));

        let (req_ctx, cancel) = context::with_cancel(&bg());
        let ctx = req(&req_ctx, "req-affinity", CheckerLifetime::TEMPORARY);

        // First call acquires.
        let (c1, release1) = pool.get_checker(&ctx, NIL);

        // Second call with same request ID while still held returns same checker (noop release).
        let (c2, release2) = pool.get_checker(&ctx, NIL);
        release2.call();
        release1.call();

        assert!(same(&c1, &c2), "same request ID should return the same checker while held");

        // After release, same request should still get the same checker (cross-release affinity).
        let (c3, release3) = pool.get_checker(&ctx, NIL);
        release3.call();

        assert!(same(&c1, &c3), "same request ID should return the same checker after release");
        cancel();
    }
}

child_test! {
    // Go: checkerpool_test.go:204 TestCheckerPoolMinCheckers
    fn min_checkers() {
        // Requesting maxCheckers=1 should be clamped to 2.
        let (_session, pool) = setup_checker_pool_session(opts(1, 10));
        assert_eq!(pool.opts.max_checkers, 2);
        assert_eq!(pool.checkers.borrow().len(), 2);
    }
}

child_test! {
    // Go: checkerpool_test.go:212 TestCheckerPoolDefaultIdleTimeout
    fn default_idle_timeout() {
        // Zero idle timeout should default to 30s.
        let (_session, pool) = setup_checker_pool_session(opts(4, 0));
        assert_eq!(pool.opts.idle_timeout, Duration::from_secs(30));
    }
}

child_test! {
    // Go: checkerpool_test.go:303 TestCheckerPoolCanceledCheckerDisposal
    fn canceled_checker_disposal() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 30));
        let source_file = pool.program.get_source_file("/src/index.ts").expect("source file").root;
        let _guard = ts_goport::program::ls_program::enter(pool.program);

        // Acquire a query checker and cancel it.
        let ctx = req(&bg(), "cancel-test", CheckerLifetime::TEMPORARY);
        let (c, release) = pool.get_checker(&ctx, NIL);

        let (canceled_ctx, cancel) = context::with_cancel(&bg());
        cancel();
        c.borrow_mut().get_diagnostics_exported(&canceled_ctx, source_file);
        assert!(c.borrow().was_canceled());

        // Release should dispose the canceled checker.
        release.call();

        // Next request should get a fresh checker.
        let ctx2 = req(&bg(), "after-cancel", CheckerLifetime::TEMPORARY);
        let (c2, release2) = pool.get_checker(&ctx2, NIL);
        assert!(!same(&c2, &c), "should get a new checker, not the canceled one");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:339 TestCheckerPoolRequestAssociationCleanupOnDisposal
    fn request_association_cleanup_on_disposal() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 5));
        let _guard = ts_goport::program::ls_program::enter(pool.program);

        // Create a query checker with a request association.
        let (req_ctx, req_cancel) = context::with_cancel(&bg());
        let ctx = req(&req_ctx, "assoc-cleanup-req", CheckerLifetime::TEMPORARY);
        let (c, release) = pool.get_checker(&ctx, NIL);

        // Cancel the checker to trigger disposal on release.
        let (canceled_ctx, cancel) = context::with_cancel(&bg());
        cancel();
        let source_file = pool.program.get_source_file("/src/index.ts").expect("source file").root;
        c.borrow_mut().get_diagnostics_exported(&canceled_ctx, source_file);
        assert!(c.borrow().was_canceled());

        release.call();

        // Request association should be cleared after checker disposal.
        assert!(
            !pool.request_associations.borrow().contains_key("assoc-cleanup-req"),
            "request association should be cleared after checker disposal"
        );
        // Go: defer reqCancel()
        req_cancel();
    }
}

child_test! {
    // Go: checkerpool_test.go:502 TestCheckerPoolLifetimeMismatchIgnoresAssociation
    fn lifetime_mismatch_ignores_association() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let (req_ctx, req_cancel) = context::with_cancel(&bg());

        // Acquire a diagnostics checker with request ID "mixed".
        let ctx_diag = req(&req_ctx, "mixed", CheckerLifetime::DIAGNOSTICS);
        let (c_diag, release_diag) = pool.get_checker(&ctx_diag, NIL);
        assert!(
            checker_at(&pool, 0).is_some_and(|x| same(&x, &c_diag)),
            "diagnostics checker should be at index 0"
        );
        release_diag.call();

        // Now use the same request ID but with query purpose.
        let ctx_query = req(&req_ctx, "mixed", CheckerLifetime::TEMPORARY);
        let (c_query, release_query) = pool.get_checker(&ctx_query, NIL);
        assert!(!same(&c_query, &c_diag), "query should not reuse the diagnostics checker");

        assert!(
            !checker_at(&pool, 0).is_some_and(|x| same(&x, &c_query)),
            "query checker should not be at diagnostics index 0"
        );
        release_query.call();
        req_cancel();
    }
}

child_test! {
    // Go: checkerpool_test.go:543 TestCheckerPoolNoRequestID
    fn no_request_id() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));

        // Calls without a request ID should still work (e.g., callhierarchy uses context.Background()).
        let ctx = bg();

        let (_c1, release1) = pool.get_checker(&ctx, NIL);
        release1.call();

        let (_c2, release2) = pool.get_checker(&ctx, NIL);
        release2.call();

        // Without request ID, no affinity guarantee — just verify it doesn't crash.
    }
}

child_test! {
    // Go: checkerpool_test.go:561 TestCheckerPoolDiagnosticsCrossReleaseAffinity
    fn diagnostics_cross_release_affinity() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let (req_ctx, req_cancel) = context::with_cancel(&bg());
        let ctx = req(&req_ctx, "diag-affinity", CheckerLifetime::DIAGNOSTICS);

        let (c1, release1) = pool.get_checker(&ctx, NIL);
        assert!(checker_at(&pool, 0).is_some_and(|x| same(&x, &c1)), "should be the diagnostics checker");
        release1.call();

        // Same request reacquiring diagnostics should get the same checker.
        let (c2, release2) = pool.get_checker(&ctx, NIL);
        assert!(same(&c2, &c1), "same diagnostics request should get the same checker after release");
        release2.call();
        req_cancel();
    }
}

child_test! {
    // Go: checkerpool_test.go:589 TestCheckerPoolDiscardKeepsIdleCheckers
    // PORT: the Go 60 s fake sleep at the end is left out (see the module comment).
    fn discard_keeps_idle_checkers() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 30));

        // Create both a diagnostics and a query checker.
        let (c1, release1) = pool.get_checker(&req(&bg(), "obs-diag", CheckerLifetime::DIAGNOSTICS), NIL);
        release1.call();

        let (c2, release2) = pool.get_checker(&req(&bg(), "obs-query", CheckerLifetime::TEMPORARY), NIL);
        release2.call();

        // Both checkers should exist before Discard.
        assert!(checker_at(&pool, 0).is_some(), "diagnostics checker should exist");

        // Discard should keep idle checkers alive and just stop the cleanup timer.
        pool.discard();

        assert!(
            checker_at(&pool, 0).is_some_and(|x| same(&x, &c1)),
            "diagnostics checker should survive Discard"
        );
        assert!(query_index(&pool, &c2) > 0, "query checker should survive Discard");
        assert!(pool.cleanup_timer.borrow().is_none(), "cleanup timer should be stopped after Discard");
    }
}

child_test! {
    // Go: checkerpool_test.go:646 TestCheckerPoolDiscardHeldCheckerSurvivesRelease
    // PORT: the Go 60 s fake sleep at the end is left out.
    fn discard_held_checker_survives_release() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 30));

        // Acquire a checker and hold it.
        let (c, release) = pool.get_checker(&req(&bg(), "held-obs", CheckerLifetime::TEMPORARY), NIL);

        // Find which slot it's in.
        let held_index = query_index(&pool, &c);
        assert!(held_index > 0, "should find the held checker");

        // Discard while checker is held — should NOT dispose it.
        pool.discard();

        assert!(
            checker_at(&pool, held_index).is_some_and(|x| same(&x, &c)),
            "held checker should survive Discard"
        );

        // Release — checker should remain alive on a discarded pool.
        release.call();

        assert!(
            checker_at(&pool, held_index).is_some_and(|x| same(&x, &c)),
            "checker should persist after release on discarded pool"
        );
    }
}

child_test! {
    // Go: checkerpool_test.go:699 TestCheckerPoolDiscardStillFunctional
    fn discard_still_functional() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 30));
        pool.discard();

        // Pool should still work — GetChecker should create a fresh checker.
        let (c, release) = pool.get_checker(&req(&bg(), "post-obs", CheckerLifetime::TEMPORARY), NIL);

        // Find the slot.
        let idx = query_index(&pool, &c);
        assert!(idx > 0, "checker should be in a query slot");

        // Release — checker should persist on discarded pool (no cleanup timer).
        release.call();

        assert!(
            checker_at(&pool, idx).is_some_and(|x| same(&x, &c)),
            "checker should persist after release on discarded pool"
        );

        // Re-acquire — should get the same checker back.
        let (c2, release2) = pool.get_checker(&req(&bg(), "post-obs-2", CheckerLifetime::TEMPORARY), NIL);
        assert!(same(&c2, &c), "should get the same checker on discarded pool");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:745 TestCheckerPoolDiagnosticsCheckerStableIdentity
    fn diagnostics_checker_stable_identity() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        // Acquire the diagnostics checker.
        let (c1, release1) = pool.get_checker(&req(&bg(), "diag-stable-1", CheckerLifetime::DIAGNOSTICS), NIL);
        release1.call();

        // Re-acquire before idle timeout — should be the same instance.
        let (c2, release2) = pool.get_checker(&req(&bg(), "diag-stable-2", CheckerLifetime::DIAGNOSTICS), NIL);
        assert!(same(&c2, &c1), "diagnostics checker should be the same instance before idle timeout");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:772 TestCheckerPoolDiagnosticsCheckerSurvivesDiscard
    fn diagnostics_checker_survives_discard() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        // Create the diagnostics checker.
        let (c, release) = pool.get_checker(&req(&bg(), "diag-discard", CheckerLifetime::DIAGNOSTICS), NIL);
        release.call();

        pool.discard();

        // Diagnostics checker should survive Discard.
        assert!(
            checker_at(&pool, 0).is_some_and(|x| same(&x, &c)),
            "diagnostics checker should survive Discard"
        );

        // Should still be acquirable and be the same instance.
        let (c2, release2) = pool.get_checker(&req(&bg(), "diag-discard-2", CheckerLifetime::DIAGNOSTICS), NIL);
        assert!(same(&c2, &c), "diagnostics checker identity should be stable after Discard");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:806 TestCheckerPoolDiagnosticsCheckerIndependentFromQuery
    fn diagnostics_checker_independent_from_query() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        // Acquire diagnostics and query checkers.
        let (diag_c, diag_release) = pool.get_checker(&req(&bg(), "diag-indep", CheckerLifetime::DIAGNOSTICS), NIL);
        let (query_c, query_release) = pool.get_checker(&req(&bg(), "query-indep", CheckerLifetime::TEMPORARY), NIL);

        // They should be different checker instances.
        assert!(!same(&diag_c, &query_c), "diagnostics and query checkers should be different");

        diag_release.call();
        query_release.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:833 TestCheckerPoolAPICheckerStableIdentity
    // PORT: the Go 60 s fake sleep (and the third acquire after it) is left out.
    fn api_checker_stable_identity() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let ctx = core_context::with_checker_lifetime(&bg(), CheckerLifetime::API);
        let (c1, release1) = pool.get_checker(&ctx, NIL);
        release1.call();

        let (c2, release2) = pool.get_checker(&ctx, NIL);
        assert!(same(&c2, &c1), "API checker should be the same instance");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:862 TestCheckerPoolAPICheckerSurvivesDiscard
    fn api_checker_survives_discard() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let ctx = core_context::with_checker_lifetime(&bg(), CheckerLifetime::API);
        let (c, release) = pool.get_checker(&ctx, NIL);
        release.call();

        pool.discard();

        assert!(
            pool.persistent_checker.borrow().as_ref().is_some_and(|x| same(x, &c)),
            "API checker should survive Discard"
        );

        let (c2, release2) = pool.get_checker(&ctx, NIL);
        assert!(same(&c2, &c), "API checker identity should be stable after Discard");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:889 TestCheckerPoolAllThreeIndependent
    fn all_three_independent() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let ded_ctx = req(&bg(), "ded-req", CheckerLifetime::DIAGNOSTICS);
        let tmp_ctx = req(&bg(), "tmp-req", CheckerLifetime::TEMPORARY);
        let per_ctx = core_context::with_checker_lifetime(&bg(), CheckerLifetime::API);

        let (ded_c, ded_release) = pool.get_checker(&ded_ctx, NIL);
        let (tmp_c, tmp_release) = pool.get_checker(&tmp_ctx, NIL);
        let (per_c, per_release) = pool.get_checker(&per_ctx, NIL);

        assert!(!same(&ded_c, &tmp_c), "diagnostics and temporary should be different");
        assert!(!same(&ded_c, &per_c), "diagnostics and API should be different");
        assert!(!same(&tmp_c, &per_c), "temporary and API should be different");

        ded_release.call();
        tmp_release.call();
        per_release.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:919 TestCheckerPoolFileAffinity
    fn file_affinity() {
        let (session, pool) = test_pool(opts(4, 10), opts(4, 30));
        let source_file = program(&session, "file:///src/index.ts")
            .get_source_file("/src/index.ts")
            .expect("source file")
            .root;

        // First query with a file should create a checker and associate it.
        let (c1, release1) = pool.get_checker(&req(&bg(), "file-aff-1", CheckerLifetime::TEMPORARY), source_file);
        release1.call();

        // Second query with the same file (different request) should get the same checker via file affinity.
        let (c2, release2) = pool.get_checker(&req(&bg(), "file-aff-2", CheckerLifetime::TEMPORARY), source_file);
        assert!(same(&c2, &c1), "same file should return the same checker via file affinity");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:949 TestCheckerPoolMultipleConcurrentQueryCheckers
    // PORT: the blocked 4th request is left out (see the module comment).
    fn multiple_concurrent_query_checkers() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        // Acquire 3 query checkers concurrently (all slots).
        let (c1, release1) = pool.get_checker(&req(&bg(), "multi-q-1", CheckerLifetime::TEMPORARY), NIL);
        let (c2, release2) = pool.get_checker(&req(&bg(), "multi-q-2", CheckerLifetime::TEMPORARY), NIL);
        let (c3, release3) = pool.get_checker(&req(&bg(), "multi-q-3", CheckerLifetime::TEMPORARY), NIL);

        // All three should be distinct checkers.
        assert!(!same(&c1, &c2), "concurrent query checkers should be distinct (1 vs 2)");
        assert!(!same(&c1, &c3), "concurrent query checkers should be distinct (1 vs 3)");
        assert!(!same(&c2, &c3), "concurrent query checkers should be distinct (2 vs 3)");

        // None should be the diagnostics checker at index 0.
        let diag = checker_at(&pool, 0);
        assert!(
            !diag.as_ref().is_some_and(|d| same(d, &c1) || same(d, &c2) || same(d, &c3)),
            "query checkers should not occupy the diagnostics slot"
        );

        release1.call();
        release2.call();
        release3.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:1032 TestCheckerPoolDefaultMaxCheckers
    // PORT: Go also checks `cap(pool.querySem) == 3`; the Rust semaphore is
    // private.
    fn default_max_checkers() {
        // Zero MaxCheckers should default to 4.
        let (_session, pool) = setup_checker_pool_session(opts(0, 10));
        assert_eq!(pool.opts.max_checkers, 4);
        assert_eq!(pool.checkers.borrow().len(), 4);
    }
}

child_test! {
    // Go: checkerpool_test.go:1106 TestCheckerPoolDiscardIdempotent
    fn discard_idempotent() {
        let (_session, pool) = test_pool(opts(2, 10), opts(4, 30));

        // Create a checker so there's something to discard.
        let (_c, release) = pool.get_checker(&req(&bg(), "idem-q", CheckerLifetime::TEMPORARY), NIL);
        release.call();

        // First discard should keep idle checkers alive.
        pool.discard();
        let has_checker = pool.checkers.borrow().iter().any(Option::is_some);
        assert!(has_checker, "first Discard should keep idle checkers alive");

        // Second discard should be a no-op (no panic, no state corruption).
        pool.discard();

        // Pool should still be functional after double Discard.
        let (_c2, release2) = pool.get_checker(&req(&bg(), "post-idem", CheckerLifetime::TEMPORARY), NIL);
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:1149 TestCheckerPoolGetGlobalDiagnosticsEmpty
    fn get_global_diagnostics_empty() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));
        // Before any checker is used, global diagnostics should be empty.
        assert_eq!(pool.get_global_diagnostics().len(), 0, "global diagnostics should be empty initially");
    }
}

child_test! {
    // Go: checkerpool_test.go:1158 TestCheckerPoolTakeNewGlobalDiagnostics
    fn take_new_global_diagnostics() {
        let (_session, pool) = setup_checker_pool_session(opts(4, 10));

        // Initially, no new globals.
        assert!(!pool.take_new_global_diagnostics(), "should report no new globals initially");

        // Use a checker and trigger diagnostics, then release to run the merge.
        let ctx = req(&bg(), "global-diag-req", CheckerLifetime::TEMPORARY);
        let source_file = pool.program.get_source_file("/src/index.ts").expect("source file").root;
        {
            let _guard = ts_goport::program::ls_program::enter(pool.program);
            let (c, release) = pool.get_checker(&ctx, source_file);
            c.borrow_mut().get_diagnostics_exported(&ctx, source_file);
            release.call();
        }

        let _first_take = pool.take_new_global_diagnostics();
        // After taking, a second call should always return false (flag is reset).
        assert!(
            !pool.take_new_global_diagnostics(),
            "TakeNewGlobalDiagnostics should reset after first call"
        );

        // Releasing the same checker again with the same state should not set the flag.
        let ctx2 = req(&bg(), "global-diag-req-2", CheckerLifetime::TEMPORARY);
        {
            let _guard = ts_goport::program::ls_program::enter(pool.program);
            let (c2, release2) = pool.get_checker(&ctx2, source_file);
            c2.borrow_mut().get_diagnostics_exported(&ctx2, source_file);
            release2.call();
        }

        assert!(
            !pool.take_new_global_diagnostics(),
            "should not report new globals when checker state is unchanged"
        );
    }
}

child_test! {
    // Go: checkerpool_test.go:1195 TestCheckerPoolAPICheckerDisposedOnCancel
    fn api_checker_disposed_on_cancel() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));
        let source_file = pool.program.get_source_file("/src/index.ts").expect("source file").root;
        let _guard = ts_goport::program::ls_program::enter(pool.program);

        let ctx = core_context::with_checker_lifetime(&bg(), CheckerLifetime::API);
        let (c, release) = pool.get_checker(&ctx, NIL);

        // Cancel the API checker.
        let (canceled_ctx, cancel) = context::with_cancel(&bg());
        cancel();
        c.borrow_mut().get_diagnostics_exported(&canceled_ctx, source_file);
        assert!(c.borrow().was_canceled());

        // Releasing a canceled API checker must drop it so it isn't reused.
        release.call();
        assert!(
            pool.persistent_checker.borrow().is_none(),
            "canceled API checker should be dropped on release"
        );

        // Next API acquisition gets a fresh, usable checker rather than panicking.
        let (c2, release2) = pool.get_checker(&ctx, NIL);
        assert!(!same(&c2, &c), "should get a fresh API checker after cancellation");
        release2.call();
    }
}

child_test! {
    // Go: checkerpool_test.go:1232 TestCheckerPoolNonCancelableContextNoAffinity
    fn non_cancelable_context_no_affinity() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        // A context that carries a request ID but can never be canceled
        // (ctx.Done() == nil) must not register a request association.
        let ctx = req(&bg(), "uncancelable-req", CheckerLifetime::TEMPORARY);
        assert!(ctx.done().is_none(), "test precondition: context must be non-cancelable");

        let (_c, release) = pool.get_checker(&ctx, NIL);
        release.call();

        assert_eq!(
            pool.request_associations.borrow().len(),
            0,
            "non-cancelable context must not grow requestAssociations"
        );
    }
}

child_test! {
    // Go: checkerpool_test.go:1260 TestCheckerPoolCleanupAfterDiscardIsNoop
    fn cleanup_after_discard_is_noop() {
        let (_session, pool) = test_pool(opts(4, 10), opts(4, 30));

        let (_c, release) = pool.get_checker(&req(&bg(), "discard-cleanup", CheckerLifetime::TEMPORARY), NIL);
        release.call();

        pool.discard();

        // Simulate the timer callback firing after Discard(). It must be a no-op and must not
        // re-arm the cleanup timer, which would keep the discarded pool alive.
        pool.cleanup_idle_checkers();

        assert!(
            pool.cleanup_timer.borrow().is_none(),
            "cleanup must not reschedule a timer on a discarded pool"
        );
        let has_checker = pool.checkers.borrow().iter().any(Option::is_some);
        assert!(has_checker, "idle checkers must survive cleanup on a discarded pool");
    }
}
