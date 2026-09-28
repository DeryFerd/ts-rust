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
//! `GOPORT_THP_GUARD` selects the mode: `0` does nothing, `force` always
//! turns THP off, and any other value (or no value) checks the memory.
//! `GOPORT_THP_GUARD_MIB` changes the limit (`DEFAULT_MIN_FREE_MIB`; a
//! value that does not parse keeps the default). `GOPORT_THP_GUARD_DEBUG=1`
//! prints the decision and its inputs as one line on stderr.

/// The guard turns THP off when less than this many MiB are free in
/// blocks of 2 MiB or more. An effect emit faults about 700 huge pages
/// (1.4 GiB). In perf11's state with 0.4 to 1.3 GB free in such blocks,
/// THP was 4% to 13% slower than 4 KiB pages.
const DEFAULT_MIN_FREE_MIB: u64 = 1024;

/// The smallest `/proc/buddyinfo` order that holds a whole 2 MiB huge page
/// (512 pages of 4 KiB). The guard runs only on x86-64, where both sizes
/// are fixed.
const HUGE_ORDER: usize = 9;

/// Bytes in one page of the buddy allocator.
const PAGE_BYTES: u64 = 4096;

/// Call first in `main`, before the first heap allocation: jemalloc maps
/// and touches its first memory at that allocation. The default path
/// allocates nothing (stack buffers only). Setting a `GOPORT_THP_GUARD*`
/// variable allocates its value first.
///
/// Checks, in order, and stops at the first that says to keep THP:
/// 1. `GOPORT_THP_GUARD` (see the module comment).
/// 2. `PR_GET_THP_DISABLE`: THP is already off (the parent turned it off,
///    or this run is the exec of `set_malloc_tunables`: the flag stays set
///    across `execve`).
/// 3. `enabled` and `defrag` in `/sys/kernel/mm/transparent_hugepage`
///    (`thp_goes_off`).
/// 4. `/proc/buddyinfo`: the free memory in blocks of 2 MiB or more, in
///    all nodes and zones, against the limit.
///
/// A file that cannot be read keeps THP on. The flag stays set for the
/// whole process and its children. The memory is read only at start, so a
/// long `--lsp` or `--watch` run keeps the first decision.
pub fn thp_guard() {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        use nix::sys::prctl::{get_thp_disable, set_thp_disable};
        let debug = std::env::var_os("GOPORT_THP_GUARD_DEBUG").is_some_and(|v| v != "0");
        let say = |args: std::fmt::Arguments<'_>| {
            if debug {
                eprintln!("goport thp_guard: {args}");
            }
        };
        match std::env::var_os("GOPORT_THP_GUARD") {
            Some(mode) if mode == "0" => return say(format_args!("THP kept (GOPORT_THP_GUARD=0)")),
            Some(mode) if mode == "force" => {
                let ok = set_thp_disable(true).is_ok();
                return say(format_args!(
                    "THP off (GOPORT_THP_GUARD=force, prctl ok {ok})"
                ));
            }
            _ => {}
        }
        let min_free_mib: u64 = std::env::var_os("GOPORT_THP_GUARD_MIB")
            .and_then(|mib| mib.to_str()?.parse().ok())
            .unwrap_or(DEFAULT_MIN_FREE_MIB);
        if get_thp_disable().unwrap_or(true) {
            return say(format_args!("THP already off at start"));
        }
        let mut enabled = [0; 128];
        let mut defrag = [0; 128];
        // About 110 bytes per zone: room for 70 nodes of 4 zones.
        let mut buddyinfo = [0; 32 << 10];
        let (Some(enabled), Some(defrag), Some(buddyinfo)) = (
            read_small("/sys/kernel/mm/transparent_hugepage/enabled", &mut enabled),
            read_small("/sys/kernel/mm/transparent_hugepage/defrag", &mut defrag),
            read_small("/proc/buddyinfo", &mut buddyinfo),
        ) else {
            return say(format_args!(
                "THP kept (a THP file or /proc/buddyinfo cannot be read)"
            ));
        };
        let Some(free) = free_huge_bytes(buddyinfo) else {
            return say(format_args!("THP kept (/proc/buddyinfo does not parse)"));
        };
        let off = thp_goes_off(enabled, defrag, free, min_free_mib.saturating_mul(1 << 20));
        let failed = off && set_thp_disable(true).is_err();
        say(format_args!(
            "THP {} (enabled {}, defrag {}, {} MiB free in 2 MiB blocks, limit {min_free_mib} MiB{})",
            if off { "off" } else { "kept" },
            selected_mode(enabled).unwrap_or("?"),
            selected_mode(defrag).unwrap_or("?"),
            free >> 20,
            if failed { ", prctl failed" } else { "" },
        ));
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

/// True when THP must go off: a huge page fault of `MADV_HUGEPAGE` memory
/// can wait in direct compaction, and `free` (the bytes free in blocks of
/// 2 MiB or more) is less than `min_free`. `enabled` and `defrag` are the
/// text of the sysfs files, with the mode in brackets. The fault can wait
/// when `enabled` is `always` or `madvise` and `defrag` is `always`,
/// `madvise` or `defer+madvise`. With `defer` or `never`, it takes a 4 KiB
/// page when no 2 MiB block is free, so THP can stay on. False when a text
/// does not parse.
fn thp_goes_off(enabled: &str, defrag: &str, free: u64, min_free: u64) -> bool {
    matches!(selected_mode(enabled), Some("always" | "madvise"))
        && matches!(
            selected_mode(defrag),
            Some("always" | "madvise" | "defer+madvise")
        )
        && free < min_free
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
    fn thp_goes_off_only_when_a_fault_can_wait_and_memory_is_low() {
        let enabled = "always [madvise] never\n";
        let defrag = "always defer defer+madvise [madvise] never\n";
        // 1,066 MiB, from BUDDYINFO.
        let free = (1 + 29 + 477) * 2 * MIB + 13 * 4 * MIB;
        assert!(thp_goes_off(enabled, defrag, free, free + 1));
        assert!(!thp_goes_off(enabled, defrag, free, free));
        assert!(!thp_goes_off(enabled, defrag, free, 1024 * MIB));
        assert!(thp_goes_off(enabled, defrag, free, 2048 * MIB));
        // No THP, or faults that do not wait for compaction.
        let never = "always madvise [never]\n";
        assert!(!thp_goes_off(never, defrag, free, 2048 * MIB));
        for defrag in [
            "always [defer] madvise never",
            "always defer madvise [never]",
        ] {
            assert!(!thp_goes_off(enabled, defrag, free, 2048 * MIB));
        }
        for defrag in [
            "[always] defer madvise never",
            "defer [defer+madvise] madvise",
        ] {
            assert!(thp_goes_off(
                "[always] madvise never",
                defrag,
                free,
                2048 * MIB
            ));
        }
        // A text that does not parse keeps THP on.
        assert!(!thp_goes_off("madvise", defrag, free, 2048 * MIB));
    }
}
