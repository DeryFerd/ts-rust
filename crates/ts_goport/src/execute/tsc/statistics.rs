//! Go: execute/tsc/statistics.go, the `--diagnostics` and
//! `--extendedDiagnostics` table, and the `CompileTimes` of
//! execute/tsc/compile.go that the table reads.

use std::fmt::Write as _;
use std::time::Duration;

use crate::prelude::*;

// Go: execute/tsc/compile.go:65 CompileTimes
// PORT: kept here with its only reader. Go keeps `bindTime`, `checkTime`,
// `totalTime` and `emitTime` unexported; the goport binary sets them, so all
// fields are public.
#[derive(Clone, Copy, Debug, Default)]
pub struct CompileTimes {
    pub config_time: Duration,
    pub parse_time: Duration,
    pub bind_time: Duration,
    pub check_time: Duration,
    pub total_time: Duration,
    pub emit_time: Duration,
    pub build_info_read_time: Duration,
    pub changes_compute_time: Duration,
}

struct TableRow {
    name: String,
    value: String,
}

#[derive(Default)]
struct Table {
    rows: Vec<TableRow>,
}

impl Table {
    // Go: execute/tsc/statistics.go:22 add
    // PORT: Go `add` takes `any` and formats a `time.Duration` with
    // `formatDuration`. Durations use `add_duration` here.
    fn add(&mut self, name: &str, value: impl std::fmt::Display) {
        self.rows.push(TableRow {
            name: name.to_string(),
            value: value.to_string(),
        });
    }

    fn add_duration(&mut self, name: &str, value: Duration) {
        self.add(name, format_duration(value));
    }

    // Go: execute/tsc/statistics.go:29 print
    fn print(&self, w: &mut String) {
        let mut name_width = 0;
        let mut value_width = 0;
        for r in &self.rows {
            name_width = name_width.max(r.name.len());
            value_width = value_width.max(r.value.len());
        }

        for r in &self.rows {
            let _ = writeln!(
                w,
                "{:<name_width$} {:>value_width$}",
                format!("{}:", r.name),
                r.value,
                name_width = name_width + 1,
            );
        }
    }
}

// Go: execute/tsc/statistics.go:42 formatDuration
fn format_duration(d: Duration) -> String {
    format!("{:.3}s", d.as_secs_f64())
}

// PORT: Go execute/tsc/statistics.go:46 `identifierCount` has no caller
// (`statisticsFromProgram` uses `Program.IdentifierCount`), so it is not
// ported.

// Go: execute/tsc/statistics.go:54 Statistics
#[derive(Clone, Debug, Default)]
pub struct Statistics {
    is_aggregate: bool,
    pub projects: i32,
    pub projects_built: i32,
    pub timestamp_updates: i32,
    files: i32,
    lines: i32,
    identifiers: i32,
    symbols: i32,
    types: i32,
    instantiations: i32,
    memory_used: u64,
    memory_allocs: u64,
    compile_times: Option<CompileTimes>,
}

/// Go `runtime.MemStats`, the two fields that `statisticsFromProgram` reads.
#[derive(Clone, Copy, Debug, Default)]
pub struct MemStats {
    /// Go `Alloc`: bytes of live heap objects.
    pub alloc: u64,
    /// Go `Mallocs`: count of heap objects allocated.
    pub mallocs: u64,
}

/// Go `runtime.GC(); runtime.GC(); runtime.ReadMemStats(&memStats)`.
// PORT: Rust has no heap statistics, and the crate forbids the `unsafe` a
// counting global allocator needs. `alloc` is the resident set size
// (`VmRSS` in /proc/self/status, 0 where that file does not exist), and
// `mallocs` is 0. Both are process values that never match Go anyway.
#[must_use]
pub fn read_mem_stats() -> MemStats {
    let alloc = std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status.lines().find_map(|line| {
                let kib = line.strip_prefix("VmRSS:")?.trim().strip_suffix("kB")?;
                kib.trim().parse::<u64>().ok()
            })
        })
        .map_or(0, |kib| kib * 1024);
    MemStats { alloc, mallocs: 0 }
}

// Go: execute/tsc/statistics.go:70 statisticsFromProgram
// PORT: Go reads the program and the compile times from `EmitInput`. The
// program is the installed process program here.
#[must_use]
pub fn statistics_from_program(compile_times: &CompileTimes, mem_stats: &MemStats) -> Statistics {
    Statistics {
        files: source_files().len() as i32,
        lines: crate::program::line_count(),
        identifiers: crate::program::identifier_count(),
        symbols: crate::program::symbol_count(),
        types: crate::program::type_count(),
        instantiations: crate::program::instantiation_count(),
        memory_used: mem_stats.alloc,
        memory_allocs: mem_stats.mallocs,
        compile_times: Some(*compile_times),
        ..Statistics::default()
    }
}

impl Statistics {
    // Go: execute/tsc/statistics.go:84 Report
    // PORT: the `CommandLineTesting` hooks are test-only and not ported.
    pub fn report(&self, w: &mut String) {
        let mut table = Table::default();
        let mut prefix = "";

        if self.is_aggregate {
            prefix = "Aggregate ";
            table.add("Projects in scope", self.projects);
            table.add("Projects built", self.projects_built);
            table.add("Timestamps only updates", self.timestamp_updates);
        }
        table.add(&format!("{prefix}Files"), self.files);
        table.add(&format!("{prefix}Lines"), self.lines);
        table.add(&format!("{prefix}Identifiers"), self.identifiers);
        table.add(&format!("{prefix}Symbols"), self.symbols);
        table.add(&format!("{prefix}Types"), self.types);
        table.add(&format!("{prefix}Instantiations"), self.instantiations);
        table.add(
            &format!("{prefix}Memory used"),
            format!("{}K", self.memory_used / 1024),
        );
        table.add(&format!("{prefix}Memory allocs"), self.memory_allocs);
        // Go dereferences the pointer; a nil one panics there.
        let compile_times = self
            .compile_times
            .expect("statistics without compile times");
        if !compile_times.config_time.is_zero() {
            table.add_duration(&format!("{prefix}Config time"), compile_times.config_time);
        }
        if !compile_times.build_info_read_time.is_zero() {
            table.add_duration(
                &format!("{prefix}BuildInfo read time"),
                compile_times.build_info_read_time,
            );
        }
        table.add_duration(&format!("{prefix}Parse time"), compile_times.parse_time);
        if !compile_times.bind_time.is_zero() {
            table.add_duration(&format!("{prefix}Bind time"), compile_times.bind_time);
        }
        if !compile_times.check_time.is_zero() {
            table.add_duration(&format!("{prefix}Check time"), compile_times.check_time);
        }
        if !compile_times.emit_time.is_zero() {
            table.add_duration(&format!("{prefix}Emit time"), compile_times.emit_time);
        }
        if !compile_times.changes_compute_time.is_zero() {
            table.add_duration(
                &format!("{prefix}Changes compute time"),
                compile_times.changes_compute_time,
            );
        }
        table.add_duration(&format!("{prefix}Total time"), compile_times.total_time);
        table.print(w);
    }

    // Go: execute/tsc/statistics.go:130 Aggregate
    pub fn aggregate(&mut self, stat: &Statistics) {
        self.is_aggregate = true;
        let compile_times = self.compile_times.get_or_insert_with(CompileTimes::default);
        // Aggregate statistics
        self.files += stat.files;
        self.lines += stat.lines;
        self.identifiers += stat.identifiers;
        self.symbols += stat.symbols;
        self.types += stat.types;
        self.instantiations += stat.instantiations;
        self.memory_used += stat.memory_used;
        self.memory_allocs += stat.memory_allocs;
        let stat_times = stat
            .compile_times
            .expect("statistics without compile times");
        compile_times.config_time += stat_times.config_time;
        compile_times.build_info_read_time += stat_times.build_info_read_time;
        compile_times.parse_time += stat_times.parse_time;
        compile_times.bind_time += stat_times.bind_time;
        compile_times.check_time += stat_times.check_time;
        compile_times.emit_time += stat_times.emit_time;
        compile_times.changes_compute_time += stat_times.changes_compute_time;
    }

    // Go: execute/tsc/statistics.go:155 SetTotalTime
    pub fn set_total_time(&mut self, total_time: Duration) {
        self.compile_times
            .get_or_insert_with(CompileTimes::default)
            .total_time = total_time;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Go pads names left-aligned to the widest name plus the colon, and
    // values right-aligned to the widest value.
    #[test]
    fn table_print_matches_go_widths() {
        let mut table = Table::default();
        table.add("Files", 750);
        table.add("Memory used", "165135K");
        table.add_duration("Changes compute time", Duration::from_micros(33_400));
        let mut out = String::new();
        table.print(&mut out);
        assert_eq!(
            out,
            "Files:                    750\n\
             Memory used:          165135K\n\
             Changes compute time:  0.033s\n"
        );
    }
}
