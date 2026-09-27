//! Go: execute/tsc/statistics.go, the `--diagnostics` and
//! `--extendedDiagnostics` table.

use std::fmt::Write as _;
use std::time::Duration;

use crate::frontend::json::{
    JsonDecoder, JsonError, JsonToken, MarshalerTo, json_unmarshal_decode,
};
use crate::prelude::*;

use super::compile::CompileTimes;
// PORT: testing (`report_to`)
use super::compile::{CommandLineTesting, Writer, write_str};

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
    // Go: execute/tsc/statistics.go:84 Report, the table part.
    // PORT: this writes the table to a string. `report_to` is Go `Report`
    // with the writer and the `CommandLineTesting` hooks.
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

    // Go: execute/tsc/statistics.go:84 Report
    // PORT: testing. Go `defer testing.OnStatisticsEnd(w)` runs after the
    // table is written.
    pub fn report_to(&self, w: &Writer, testing: Option<Rc<dyn CommandLineTesting>>) {
        if let Some(testing) = &testing {
            testing.on_statistics_start(w);
        }
        let mut text = String::new();
        self.report(&mut text);
        write_str(w, &text);
        if let Some(testing) = &testing {
            testing.on_statistics_end(w);
        }
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

// PORT: a build worker (execute/build/worker.rs) runs a project's
// `EmitAndReportStatistics` in its own process. It sends the statistics to
// the orchestrator for `Aggregate` (build/buildtask.go:102) in this JSON
// form: the fields that `statisticsFromProgram` sets, with durations in
// nanoseconds. Go has no such form.
impl MarshalerTo for Statistics {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        let _ = write!(
            enc,
            "{{\"files\":{},\"lines\":{},\"identifiers\":{},\"symbols\":{},\"types\":{},\
             \"instantiations\":{},\"memoryUsed\":{},\"memoryAllocs\":{},\"compileTimes\":",
            self.files,
            self.lines,
            self.identifiers,
            self.symbols,
            self.types,
            self.instantiations,
            self.memory_used,
            self.memory_allocs,
        );
        match self.compile_times {
            Some(mut times) => {
                enc.push('{');
                for (i, (name, value)) in compile_times_fields(&mut times).into_iter().enumerate() {
                    if i > 0 {
                        enc.push(',');
                    }
                    let _ = write!(enc, "\"{name}\":{}", value.as_nanos());
                }
                enc.push('}');
            }
            None => enc.push_str("null"),
        }
        enc.push('}');
        Ok(())
    }
}

/// Reads the build worker form of `Statistics` back (see its `MarshalerTo`).
/// Unknown members are skipped.
pub fn decode_statistics(dec: &mut JsonDecoder<'_>) -> Result<Statistics, JsonError> {
    let mut stat = Statistics::default();
    if dec.read_token()? != JsonToken::BeginObject {
        return Err(invalid_statistics());
    }
    while dec.peek_kind() != b'}' {
        let mut key = String::new();
        json_unmarshal_decode(dec, &mut key)?;
        match key.as_str() {
            "files" => stat.files = decode_integer(dec)?,
            "lines" => stat.lines = decode_integer(dec)?,
            "identifiers" => stat.identifiers = decode_integer(dec)?,
            "symbols" => stat.symbols = decode_integer(dec)?,
            "types" => stat.types = decode_integer(dec)?,
            "instantiations" => stat.instantiations = decode_integer(dec)?,
            "memoryUsed" => stat.memory_used = decode_integer(dec)?,
            "memoryAllocs" => stat.memory_allocs = decode_integer(dec)?,
            "compileTimes" => stat.compile_times = decode_compile_times(dec)?,
            _ => dec.skip_value()?,
        }
    }
    dec.read_token()?;
    Ok(stat)
}

fn decode_compile_times(dec: &mut JsonDecoder<'_>) -> Result<Option<CompileTimes>, JsonError> {
    match dec.read_token()? {
        JsonToken::Null => return Ok(None),
        JsonToken::BeginObject => {}
        _ => return Err(invalid_statistics()),
    }
    let mut times = CompileTimes::default();
    while dec.peek_kind() != b'}' {
        let mut name = String::new();
        json_unmarshal_decode(dec, &mut name)?;
        match compile_times_fields(&mut times)
            .into_iter()
            .find(|(field, _)| *field == name)
        {
            Some((_, value)) => *value = Duration::from_nanos(decode_integer(dec)?),
            None => dec.skip_value()?,
        }
    }
    dec.read_token()?;
    Ok(Some(times))
}

/// The `CompileTimes` fields by their name in the build worker form.
fn compile_times_fields(times: &mut CompileTimes) -> [(&'static str, &mut Duration); 8] {
    [
        ("configTime", &mut times.config_time),
        ("parseTime", &mut times.parse_time),
        ("bindTime", &mut times.bind_time),
        ("checkTime", &mut times.check_time),
        ("totalTime", &mut times.total_time),
        ("emitTime", &mut times.emit_time),
        ("buildInfoReadTime", &mut times.build_info_read_time),
        ("changesComputeTime", &mut times.changes_compute_time),
    ]
}

/// A JSON number that must be an integer of type `T`.
fn decode_integer<T: std::str::FromStr>(dec: &mut JsonDecoder<'_>) -> Result<T, JsonError> {
    match dec.read_token()? {
        JsonToken::Number(raw) => raw.parse().map_err(|_| invalid_statistics()),
        _ => Err(invalid_statistics()),
    }
}

fn invalid_statistics() -> JsonError {
    JsonError {
        message: "invalid build worker statistics".to_string(),
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

    // The build worker form keeps every field that the report reads.
    #[test]
    fn worker_form_round_trips() {
        let stat = Statistics {
            files: 83,
            lines: 58434,
            identifiers: 49724,
            symbols: 59777,
            types: 35331,
            instantiations: 34231,
            memory_used: 62_549 * 1024,
            memory_allocs: 297_406,
            compile_times: Some(CompileTimes {
                config_time: Duration::from_nanos(1),
                parse_time: Duration::from_micros(24_000),
                check_time: Duration::from_nanos(214_000_123),
                total_time: Duration::from_millis(256),
                emit_time: Duration::from_micros(1_000),
                changes_compute_time: Duration::from_micros(16_000),
                ..CompileTimes::default()
            }),
            ..Statistics::default()
        };
        let mut json = String::new();
        stat.marshal_json_to(&mut json).unwrap();
        let mut dec = crate::frontend::json::json_new_decoder(json.as_bytes());
        let back = decode_statistics(&mut dec).unwrap();
        dec.check_eof().unwrap();
        let (mut want, mut got) = (String::new(), String::new());
        stat.report(&mut want);
        back.report(&mut got);
        assert_eq!(got, want);
        assert_eq!(format!("{back:?}"), format!("{stat:?}"));
    }
}
