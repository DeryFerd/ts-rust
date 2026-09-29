//! The THP guard: turns transparent huge pages off for this process when
//! the kernel has little free memory in 2 MiB blocks. Not a Go port.
//!
//! jemalloc runs with `thp:always,metadata_thp:always` (see `bin/goport.rs`
//! `set_malloc_tunables`), so it marks its memory `MADV_HUGEPAGE`. On clean
//! memory that is 7% to 22% faster than 4 KiB pages (perf12 THP grid). When
//! the free memory is in small blocks (for example after a file walk or a
//! build fills the dentry and inode slab), each huge page fault of that
//! memory waits in direct compaction, and a run takes 50% to 85% longer
//! (perf12: 2,600 compaction stalls in one effect emit). With THP off
//! (`prctl(PR_SET_THP_DISABLE)`), the faults take 4 KiB pages and do not
//! wait, even where jemalloc asked for huge pages.
//!
//! The guard has two parts:
//! - The start check turns THP off at once when less than the limit is free
//!   in 2 MiB blocks.
//! - Else a watcher thread reads the free memory every `POLL` and turns THP
//!   off the first time it drops below the limit. The huge pages that the
//!   run faulted before stay. The flag changes only the later faults.
//!
//! The limit is low (`DEFAULT_MIN_FREE_MIB`) because a run that finds
//! enough free 2 MiB blocks is faster with THP. perf13 on dbook, with only
//! a start check at 1 GiB, fragmented memory: query and hono started with
//! a median of 223 to 284 MiB free, and THP off made them 6% to 16%
//! slower. zod started with 272 MiB but faults about 900 MiB, and THP kept
//! made it 39% slower: the watcher is for that case. With 10 to 148 MiB
//! free at start, THP kept made effect 41% to 49% slower and query check 8
//! 3% to 12% slower.
//!
//! perf13b, a watcher at 128 MiB on fragmented memory: hono emit faulted
//! about 66 huge pages before it fired, where THP kept got all 144 with a
//! few compaction stalls, so hono was 2.2% slower than with THP kept. The
//! watcher fires later than the limit (see `POLL`); 64 MiB keeps enough
//! margin for that. In two more grids (more fragmented: most runs started
//! below 64 MiB) 64 MiB was within noise of 128 MiB or faster in every
//! cell, and tsgo -b query chain got about 90 to 130 huge pages, not 56 to
//! 99, with no compaction stall.
//!
//! `GOPORT_THP_GUARD` selects the mode: `0` does nothing, `force` always
//! turns THP off, `start` does the start check but starts no watcher, and
//! any other value (or no value) does both. `GOPORT_THP_GUARD_MIB` changes
//! the limit of both (a value that does not parse keeps the default).
//! `GOPORT_THP_GUARD_DEBUG=1` prints each decision and its inputs as one
//! line on stderr.

use std::time::Duration;

/// The guard turns THP off when less than this many MiB are free in
/// blocks of 2 MiB or more. See the module comment for the perf13 and
/// perf13b data.
const DEFAULT_MIN_FREE_MIB: u64 = 64;

/// How often the watcher reads `/proc/buddyinfo`. A run faults huge pages
/// fastest at its start: in perf13b the free memory fell up to 36 MiB
/// between two reads (effect emit and query check), so the watcher must
/// fire that far above zero to beat the first compaction stall.
const POLL: Duration = Duration::from_millis(5);

/// The watcher stops after this time, so a long `--lsp` or `--watch`
/// process does not read the memory for its whole life. The longest run of
/// the perf13 grid took 1.2 s.
const WATCH_FOR: Duration = Duration::from_secs(60);

/// The buffer for `/proc/buddyinfo`: about 110 bytes per zone, so room for
/// 70 nodes of 4 zones.
const BUDDYINFO_BYTES: usize = 32 << 10;

/// The smallest `/proc/buddyinfo` order that holds a whole 2 MiB huge page
/// (512 pages of 4 KiB). The guard runs only on x86-64, where both sizes
/// are fixed.
const HUGE_ORDER: usize = 9;

/// Bytes in one page of the buddy allocator.
const PAGE_BYTES: u64 = 4096;

/// Call first in `main`, before the first heap allocation: jemalloc maps
/// and touches its first memory at that allocation. The start check
/// allocates nothing (stack buffers only). Setting a `GOPORT_THP_GUARD*`
/// variable allocates its value first. The watcher thread start allocates,
/// after the start check.
///
/// Checks, in order, and stops at the first that says to keep THP:
/// 1. `GOPORT_THP_GUARD` (see the module comment).
/// 2. `PR_GET_THP_DISABLE`: THP is already off (the parent turned it off,
///    or this run is the exec of `set_malloc_tunables`: the flag stays set
///    across `execve`).
/// 3. `enabled` and `defrag` in `/sys/kernel/mm/transparent_hugepage`
///    (`start_step`).
/// 4. `/proc/buddyinfo`: the free memory in blocks of 2 MiB or more, in
///    all nodes and zones, against the limit. Below it, THP goes off. Else
///    the watcher starts (`watch`).
///
/// A file that cannot be read keeps THP on and starts no watcher. The flag
/// stays set for the whole process and its children.
pub fn thp_guard() {
    guard(true);
}

/// The start check of `thp_guard` without the watcher, for a process that
/// sets the jemalloc settings of the process it starts or execs
/// (`bin/tsgo.rs` `early_thp_conf`). True when THP stays on for this process
/// and its children, false when it is off (the check turned it off, or it
/// was off already). Call it before the first large allocation, like
/// `thp_guard`.
pub fn thp_start_check() -> bool {
    guard(false)
}

/// `thp_guard` with the watcher allowed when `watch`. True when THP stays
/// on (see `thp_start_check`).
fn guard(watch: bool) -> bool {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        use nix::sys::prctl::{get_thp_disable, set_thp_disable};
        let debug = std::env::var_os("GOPORT_THP_GUARD_DEBUG").is_some_and(|v| v != "0");
        let watcher = match std::env::var_os("GOPORT_THP_GUARD") {
            Some(mode) if mode == "0" => {
                say(debug, format_args!("THP kept (GOPORT_THP_GUARD=0)"));
                return true;
            }
            Some(mode) if mode == "force" => {
                let ok = set_thp_disable(true).is_ok();
                say(
                    debug,
                    format_args!("THP off (GOPORT_THP_GUARD=force, prctl ok {ok})"),
                );
                return !ok;
            }
            Some(mode) => watch && mode != "start",
            None => watch,
        };
        let min_free_mib: u64 = std::env::var_os("GOPORT_THP_GUARD_MIB")
            .and_then(|mib| mib.to_str()?.parse().ok())
            .unwrap_or(DEFAULT_MIN_FREE_MIB);
        if get_thp_disable().unwrap_or(true) {
            say(debug, format_args!("THP already off at start"));
            return false;
        }
        let mut enabled = [0; 128];
        let mut defrag = [0; 128];
        let mut buddyinfo = [0; BUDDYINFO_BYTES];
        let (Some(enabled), Some(defrag), Some(buddyinfo)) = (
            read_small("/sys/kernel/mm/transparent_hugepage/enabled", &mut enabled),
            read_small("/sys/kernel/mm/transparent_hugepage/defrag", &mut defrag),
            read_small("/proc/buddyinfo", &mut buddyinfo),
        ) else {
            say(
                debug,
                format_args!("THP kept (a THP file or /proc/buddyinfo cannot be read)"),
            );
            return true;
        };
        let Some(free) = free_huge_bytes(buddyinfo) else {
            say(
                debug,
                format_args!("THP kept (/proc/buddyinfo does not parse)"),
            );
            return true;
        };
        let min_free = min_free_mib.saturating_mul(1 << 20);
        let step = start_step(enabled, defrag, free, min_free);
        let failed = step == Start::Off && set_thp_disable(true).is_err();
        let watching = step == Start::Watch && watcher && start_watcher(min_free, debug);
        say(
            debug,
            format_args!(
                "THP {} (enabled {}, defrag {}, {} MiB free in 2 MiB blocks, limit {min_free_mib} MiB{}{})",
                if step == Start::Off { "off" } else { "kept" },
                selected_mode(enabled).unwrap_or("?"),
                selected_mode(defrag).unwrap_or("?"),
                free >> 20,
                if failed { ", prctl failed" } else { "" },
                if watching { ", watcher started" } else { "" },
            ),
        );
        step != Start::Off || failed
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    {
        let _ = watch;
        true
    }
}

/// Prints `args` as one `goport thp_guard:` line on stderr when `debug`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn say(debug: bool, args: std::fmt::Arguments<'_>) {
    if debug {
        eprintln!("goport thp_guard: {args}");
    }
}

/// Starts the `watch` thread. False when the thread cannot start. The
/// buddyinfo buffer is made here, on the heap: glibc puts the static TLS
/// (79 to 99 KiB in perf13b) at the top of each thread stack, so a small
/// stack (a 128 KiB one, or `RUST_MIN_STACK`) had too little room for it.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn start_watcher(min_free: u64, debug: bool) -> bool {
    let buddyinfo = vec![0; BUDDYINFO_BYTES];
    std::thread::Builder::new()
        .name("thp-guard".into())
        .spawn(move || watch(min_free, debug, buddyinfo))
        .is_ok()
}

/// The watcher thread: reads `/proc/buddyinfo` into `buddyinfo` every
/// `POLL` and follows `watch_step`. It turns THP off at most once, then
/// ends. It allocates nothing.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn watch(min_free: u64, debug: bool, mut buddyinfo: Vec<u8>) {
    let start = std::time::Instant::now();
    loop {
        std::thread::sleep(POLL);
        let free = read_small("/proc/buddyinfo", &mut buddyinfo).and_then(free_huge_bytes);
        let elapsed = start.elapsed();
        match (watch_step(elapsed, free, min_free), free) {
            (Watch::Wait, _) => {}
            (Watch::Off, free) => {
                let ok = nix::sys::prctl::set_thp_disable(true).is_ok();
                return say(
                    debug,
                    format_args!(
                        "THP off by the watcher after {} ms ({} MiB free in 2 MiB blocks, prctl ok {ok})",
                        elapsed.as_millis(),
                        free.unwrap_or(0) >> 20,
                    ),
                );
            }
            (Watch::Stop, None) => {
                return say(
                    debug,
                    format_args!(
                        "watcher stopped, THP kept (/proc/buddyinfo cannot be read or does not parse)"
                    ),
                );
            }
            (Watch::Stop, Some(free)) => {
                return say(
                    debug,
                    format_args!(
                        "watcher stopped after {} s, THP kept ({} MiB free in 2 MiB blocks)",
                        elapsed.as_secs(),
                        free >> 20,
                    ),
                );
            }
        }
    }
}

/// What the start check does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Start {
    /// Keep THP and start no watcher: a fault never waits for compaction,
    /// or a THP text does not parse.
    Keep,
    /// Turn THP off now.
    Off,
    /// Keep THP and start the watcher.
    Watch,
}

/// The start decision. A huge page fault of `MADV_HUGEPAGE` memory can
/// wait in direct compaction when `enabled` is `always` or `madvise` and
/// `defrag` is `always`, `madvise` or `defer+madvise` (the texts of the
/// sysfs files, with the mode in brackets). With `defer` or `never`, it
/// takes a 4 KiB page when no 2 MiB block is free, so THP can stay on. When
/// a fault can wait: `Off` when `free` (the bytes free in blocks of 2 MiB
/// or more) is less than `min_free`, else `Watch`.
fn start_step(enabled: &str, defrag: &str, free: u64, min_free: u64) -> Start {
    let can_wait = matches!(selected_mode(enabled), Some("always" | "madvise"))
        && matches!(
            selected_mode(defrag),
            Some("always" | "madvise" | "defer+madvise")
        );
    match (can_wait, free < min_free) {
        (false, _) => Start::Keep,
        (true, true) => Start::Off,
        (true, false) => Start::Watch,
    }
}

/// What the watcher does after one read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Watch {
    /// Read again after `POLL`.
    Wait,
    /// Turn THP off and stop.
    Off,
    /// Stop and keep THP.
    Stop,
}

/// The watcher decision after `elapsed` since it started. `free` is the
/// bytes free in blocks of 2 MiB or more, None when `/proc/buddyinfo`
/// cannot be read or does not parse. Low memory wins over the time limit.
fn watch_step(elapsed: Duration, free: Option<u64>, min_free: u64) -> Watch {
    match free {
        None => Watch::Stop,
        Some(free) if free < min_free => Watch::Off,
        Some(_) if elapsed >= WATCH_FOR => Watch::Stop,
        Some(_) => Watch::Wait,
    }
}

/// The text of the file at `path`, read into `buf` without a heap
/// allocation. None when the file cannot be read, is not UTF-8, or does not
/// fit in `buf`.
fn read_small<'a>(path: &str, buf: &'a mut [u8]) -> Option<&'a str> {
    use std::io::Read;
    let mut file = std::fs::File::open(path).ok()?;
    let mut len = 0;
    loop {
        match file.read(&mut buf[len..]).ok()? {
            0 => break,
            n => len += n,
        }
        if len == buf.len() {
            return None;
        }
    }
    std::str::from_utf8(&buf[..len]).ok()
}

/// The mode in brackets in a THP sysfs file: `madvise` in
/// `always [madvise] never`.
fn selected_mode(text: &str) -> Option<&str> {
    let (_, rest) = text.split_once('[')?;
    rest.split_once(']').map(|(mode, _)| mode)
}

/// The free bytes in blocks of order `HUGE_ORDER` or more in
/// `/proc/buddyinfo`, all lines summed. Each line is
/// `Node 0, zone   Normal  <free blocks of order 0> <order 1> ...`. None
/// when no line parses.
fn free_huge_bytes(buddyinfo: &str) -> Option<u64> {
    let mut total = None;
    for line in buddyinfo.lines() {
        let mut words = line.split_whitespace();
        if words.next() != Some("Node") || words.nth(1) != Some("zone") || words.next().is_none() {
            continue;
        }
        let mut free = 0u64;
        for (order, count) in words.enumerate() {
            let count: u64 = count.parse().ok()?;
            if order >= HUGE_ORDER {
                free = free.saturating_add(count.saturating_mul(PAGE_BYTES << order));
            }
        }
        total = Some(total.unwrap_or(0u64).saturating_add(free));
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    const MIB: u64 = 1 << 20;

    /// zbook: 1 + 29 + 477 blocks of 2 MiB and 2 + 1 + 10 of 4 MiB.
    const BUDDYINFO: &str = "\
Node 0, zone      DMA      0      1      0      0      1      1      1      1      0      1      2
Node 0, zone    DMA32    335   1658   2953   3171   2345   1679   1193    816    311     29      1
Node 0, zone   Normal 616681 607866 455781 337376 229283 129647  50350  16747   2527    477     10
";

    #[test]
    fn free_huge_bytes_sums_orders_9_and_up() {
        assert_eq!(
            free_huge_bytes(BUDDYINFO),
            Some((1 + 29 + 477) * 2 * MIB + 13 * 4 * MIB)
        );
        // Two nodes; order 11 counts 8 MiB.
        let two_nodes = "Node 0, zone Normal 5 0 0 0 0 0 0 0 0 1 0 0\n\
                         Node 1, zone Normal 0 0 0 0 0 0 0 0 0 0 0 1\n";
        assert_eq!(free_huge_bytes(two_nodes), Some(2 * MIB + 8 * MIB));
        assert_eq!(free_huge_bytes(""), None);
        assert_eq!(free_huge_bytes("Node 0, zone Normal 1 x 3\n"), None);
    }

    #[test]
    fn selected_mode_reads_the_bracketed_word() {
        assert_eq!(selected_mode("[always] madvise never\n"), Some("always"));
        assert_eq!(
            selected_mode("always defer [defer+madvise] madvise never\n"),
            Some("defer+madvise")
        );
        assert_eq!(selected_mode("always madvise never\n"), None);
    }

    #[test]
    fn start_step_turns_thp_off_only_below_the_limit_and_else_watches() {
        let enabled = "always [madvise] never\n";
        let defrag = "always defer defer+madvise [madvise] never\n";
        let limit = DEFAULT_MIN_FREE_MIB * MIB;
        assert_eq!(start_step(enabled, defrag, limit - 1, limit), Start::Off);
        assert_eq!(start_step(enabled, defrag, 0, limit), Start::Off);
        assert_eq!(start_step(enabled, defrag, limit, limit), Start::Watch);
        // perf13 fragd1: query started with 290 to 314 MiB free.
        assert_eq!(start_step(enabled, defrag, 300 * MIB, limit), Start::Watch);
        // No THP, or faults that do not wait for compaction: no watcher.
        let never = "always madvise [never]\n";
        assert_eq!(start_step(never, defrag, 0, limit), Start::Keep);
        for defrag in [
            "always [defer] madvise never",
            "always defer madvise [never]",
        ] {
            assert_eq!(start_step(enabled, defrag, 0, limit), Start::Keep);
        }
        for defrag in [
            "[always] defer madvise never",
            "defer [defer+madvise] madvise",
        ] {
            assert_eq!(
                start_step("[always] madvise never", defrag, 0, limit),
                Start::Off
            );
        }
        // A text that does not parse keeps THP on.
        assert_eq!(start_step("madvise", defrag, 0, limit), Start::Keep);
    }

    #[test]
    fn watch_step_turns_thp_off_below_the_limit_until_the_time_limit() {
        let limit = DEFAULT_MIN_FREE_MIB * MIB;
        let early = POLL;
        assert_eq!(watch_step(early, Some(limit), limit), Watch::Wait);
        assert_eq!(watch_step(early, Some(10_000 * MIB), limit), Watch::Wait);
        assert_eq!(watch_step(early, Some(limit - 1), limit), Watch::Off);
        // A file that cannot be read stops the watcher.
        assert_eq!(watch_step(early, None, limit), Watch::Stop);
        // After the time limit it stops, but low memory still turns THP off.
        assert_eq!(watch_step(WATCH_FOR, Some(limit), limit), Watch::Stop);
        assert_eq!(watch_step(WATCH_FOR, Some(0), limit), Watch::Off);
        assert_eq!(
            watch_step(WATCH_FOR - Duration::from_millis(1), Some(limit), limit),
            Watch::Wait
        );
    }
}
