//! fastmode1: the opt-in fast mode. Not in Go.
//!
//! `tsgo --fast` (the bin removes the flag before Go's option parsing) or
//! `GOPORT_FAST=1` (for every bin of the process: tsc, the LSP and the API
//! server) turns on, together:
//!
//! - more checkers: one per core, up to `MAX_CHECKERS`, and at most one per
//!   `FILES_PER_CHECKER` program files that are not declaration files
//!   (`checker_count`). An explicit `--checkers N` or `--singleThreaded`
//!   still wins, and `tsc -b` keeps Go's 4 (it can check several projects
//!   at once);
//! - lazy member tables (`GOPORT_LAZY_MEMBERS`, `checker/lazy_members.rs`);
//! - the fast name order of `some_property_reduces_to_never`
//!   (`GOPORT_FAST_NEVER_ORDER`, `checker/checker_p24.rs`);
//! - one jemalloc arena per checker (`jemalloc_layout::ArenaClaims`).
//!
//! `GOPORT_FAST_SPLIT=cost` (an experiment, off by default) replaces Go's
//! split with `cost_split`.
//!
//! Each part also has its own switch: `GOPORT_LAZY_MEMBERS=0`,
//! `GOPORT_FAST_NEVER_ORDER=0` and `GOPORT_FAST_ARENAS=0` turn that part off
//! in fast mode, and `=1` turns the first two on without it.
//!
//! Fast mode is deterministic: each file goes to the checker of Go's split
//! for the chosen count (or of the cost split with `GOPORT_FAST_SPLIT=cost`,
//! which can differ from Go's output), so the output is the same on every run
//! and, with Go's split, equals Go's `--checkers N` for that N, except where
//! lazy members or the never order change the work. `GOPORT_FAST_STEAL=1` opts in to a work-stealing
//! check pass (`steal`), which is faster on some projects but not
//! deterministic.
//!
//! The default (no flag, no variable) does none of this, so its output,
//! counts included, stays Go's. Fast mode changes the counts, and it can
//! change the output where Go's output depends on the checker count (as Go
//! with more checkers), where a stolen file changes which files share a
//! checker (from run to run), and where lazy members change the work (see
//! the lane reports, `target/continuation-r97-goport/fastmode1` and
//! `fastmode2`).

use std::cmp::Reverse;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

/// The CLI flag that `take_flag` removes.
pub const FLAG: &str = "--fast";

/// The most checkers fast mode starts by default (fastmode1: on a 16 vCPU
/// testbox, 16 checkers were the fastest on VS Code and Sentry, and 12 to
/// 16 on the other apps; more than 16 was not measured).
pub const MAX_CHECKERS: usize = 16;

/// Fast mode starts at most one checker per this many program files that
/// are not declaration files, and never fewer than Go's 4: a checker costs
/// its start and a copy of the types it reads.
pub const FILES_PER_CHECKER: usize = 32;

/// 0: not read yet, 1: off, 2: on.
static STATE: AtomicU8 = AtomicU8::new(0);

/// Set by `take_flag` for `tsc -b` (`--build` comes first in Go).
static BUILD: AtomicBool = AtomicBool::new(false);

/// Removes every `--fast` from the command line `args` (without the
/// program name) and turns fast mode on when there was one. Call before the
/// first `enabled` (tsgo `run_main` does).
pub fn take_flag(args: &mut Vec<String>) {
    let before = args.len();
    args.retain(|arg| arg != FLAG);
    if args.len() != before {
        STATE.store(2, Ordering::Relaxed);
    }
    if args
        .first()
        .is_some_and(|arg| arg == "-b" || arg == "--build")
    {
        BUILD.store(true, Ordering::Relaxed);
    }
}

/// True when fast mode is on: `--fast` (`take_flag`) or `GOPORT_FAST=1`.
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        0 => {
            let on = std::env::var("GOPORT_FAST").as_deref() == Ok("1");
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
        state => state == 2,
    }
}

/// A part switch: `name=1` turns it on, `name=0` off, else it follows fast
/// mode.
pub fn part(name: &str) -> bool {
    match std::env::var(name).as_deref() {
        Ok("1") => true,
        Ok("0") => false,
        _ => enabled(),
    }
}

/// The work-stealing check pass of fast mode, opt-in with
/// `GOPORT_FAST_STEAL=1` (`program.rs` `stealing_check`). Each checker
/// starts with Go's split of its files and, when its own queue is empty,
/// takes the last unstarted file of the queue with the most work left. A
/// stolen file's later work (emit, declaration diagnostics) goes to the
/// checker that checked it. Which checker checks a file then depends on
/// thread timing, so where Go's output depends on which files share a
/// checker, the output can change from run to run. Read once.
pub fn steal() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| enabled() && std::env::var("GOPORT_FAST_STEAL").as_deref() == Ok("1"))
}

/// One jemalloc arena per checker (`GOPORT_FAST_ARENAS`). Read once.
pub fn own_arenas() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| enabled() && part("GOPORT_FAST_ARENAS"))
}

/// The checker count of fast mode for a program with `source_files` files
/// that are not declaration files, without an explicit `--checkers`: one
/// per core (`available_parallelism`, which reads the CPU affinity and
/// cgroup quota), at most `MAX_CHECKERS`, at most one per
/// `FILES_PER_CHECKER` of those files, and at least Go's 4. Go's 4 in
/// `tsc -b`.
#[must_use]
pub fn checker_count(source_files: usize) -> usize {
    if BUILD.load(Ordering::Relaxed) {
        return 4;
    }
    static CORES: OnceLock<usize> = OnceLock::new();
    let cores = *CORES.get_or_init(|| std::thread::available_parallelism().map_or(4, Into::into));
    cores
        .min(MAX_CHECKERS)
        .min(source_files.div_ceil(FILES_PER_CHECKER))
        .max(4)
}

/// The experimental cost split (`GOPORT_FAST_SPLIT=cost`, `cost_split`) in
/// fast mode. Read once.
pub fn cost_split_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| enabled() && std::env::var("GOPORT_FAST_SPLIT").as_deref() == Ok("cost"))
}

/// The percent of an import's weight that `cost_split` adds to a checker
/// that does not read that import yet: `GOPORT_FAST_SPLIT_DEP`, default
/// `DEP_SHARE`. Read once.
fn dep_share() -> u64 {
    static SHARE: OnceLock<u64> = OnceLock::new();
    *SHARE.get_or_init(|| {
        std::env::var("GOPORT_FAST_SPLIT_DEP")
            .ok()
            .and_then(|share| share.parse().ok())
            .unwrap_or(DEP_SHARE)
    })
}

/// The default of `dep_share`. fastmode2 sweep (0 to 800, 3 rounds, VS Code
/// and Sentry at 16 checkers): 50 and 100 were the fastest, 0 the slowest.
const DEP_SHARE: u64 = 100;

/// fastmode2 experiment: a static split of `costs.len()` files over `count`
/// checkers that balances the work of the check pass. Not in Go.
///
/// - `costs[f]`: the check work of file `f`, 0 when the check skips it.
/// - `weights[f]`: the size of file `f` (Go's base weight), checked or not.
/// - `imports[f]`: the program files that `f` imports, sorted, no repeats.
///
/// The checked files go one by one, the most costly first (program order on
/// a tie), to the checker whose load after the file is the lowest (the
/// first on a tie). That load adds the file's cost and `dep_share` percent
/// of the weight of each import that the checker does not read yet: a new
/// checker must read the types of that import again. Files without cost go
/// round robin in program order. The same inputs give the same split on
/// every run. Returns the checker of each file.
#[must_use]
pub fn cost_split(
    costs: &[u64],
    weights: &[u64],
    imports: &[Vec<usize>],
    count: usize,
) -> Vec<usize> {
    let files = costs.len();
    let words = files.div_ceil(64);
    // Bit d of row c: checker c checks or imports file d.
    let mut read = vec![0u64; count * words];
    let mut load = vec![0u64; count];
    let mut checker_of = vec![usize::MAX; files];
    let mut order: Vec<usize> = (0..files).filter(|&f| costs[f] > 0).collect();
    order.sort_by_key(|&f| (Reverse(costs[f]), f));
    let share = dep_share();
    for f in order {
        let mut best = (u64::MAX, 0);
        for (checker, &checker_load) in load.iter().enumerate() {
            let row = &read[checker * words..][..words];
            let new_reads: u64 = imports[f]
                .iter()
                .filter(|&&d| row[d / 64] >> (d % 64) & 1 == 0)
                .map(|&d| weights[d])
                .sum();
            let after = checker_load + costs[f] + new_reads * share / 100;
            if after < best.0 {
                best = (after, checker);
            }
        }
        let (after, checker) = best;
        load[checker] = after;
        checker_of[f] = checker;
        let row = &mut read[checker * words..][..words];
        for &d in imports[f].iter().chain(std::iter::once(&f)) {
            row[d / 64] |= 1 << (d % 64);
        }
    }
    let mut next = 0;
    for checker in checker_of
        .iter_mut()
        .filter(|checker| **checker == usize::MAX)
    {
        *checker = next % count;
        next += 1;
    }
    checker_of
}

#[cfg(test)]
mod tests {
    use super::cost_split;

    /// The most costly file goes first; a file that shares an import with a
    /// placed file joins its checker while that costs less; files without
    /// cost go round robin.
    #[test]
    fn cost_split_balances_and_keeps_imports_together() {
        // 0 and 1 import 4 (weight 50); 2 imports nothing; 3 and 5 cost 0.
        let costs = [40, 30, 60, 0, 10, 0];
        let weights = [40, 30, 60, 5, 50, 5];
        let imports = [vec![4], vec![4], vec![], vec![], vec![], vec![]];
        let split = cost_split(&costs, &weights, &imports, 2);
        // 2 (60) on 0; 0 (40 + 50) on 1; 1 (30, 4 read) on 1; 4 (10) on 0.
        assert_eq!(split, [1, 1, 0, 0, 0, 1]);
        assert_eq!(split, cost_split(&costs, &weights, &imports, 2));
    }
}
