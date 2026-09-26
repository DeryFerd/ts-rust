//! Go: pprof/pprof.go (package `pprof`), and the parts of the Go standard
//! library package `runtime/pprof` (go1.26.4, the oracle's toolchain) that
//! it calls.
//!
//! PORT: only `BeginProfiling` and `ProfileSession.Stop` are ported. They
//! are the calls of `tscCompilation` and `tscBuildCompilation`
//! (execute/execute_tsc.rs). `CPUProfiler`, `SaveHeapProfile`,
//! `SaveAllocProfile` and `RunGC` serve the language server and are not
//! ported.
//!
//! PORT: Go `runtime/pprof` builds its profiles from samples that the Go
//! runtime takes: CPU samples on SIGPROF, and allocation samples every
//! `runtime.MemProfileRate` bytes. The port has no such sampler, so it has
//! no samples. It writes the profiles as `runtime/pprof` writes a profile
//! with no samples: the gzip-compressed `profile.proto` message with the
//! sample types, the period, the times, the executable mappings of
//! `/proc/self/maps` with their GNU build IDs, and the string table. It
//! writes no `Sample`, `Location` or `Function` message. The directory,
//! the file names, the file order and the printed lines are Go's. The pid,
//! the times, the mappings and the profile bytes never match Go, like the
//! memory statistics (execute/tsc/statistics.rs `read_mem_stats`).

use std::ffi::OsStr;
use std::fs::{DirBuilder, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, FileExt};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use flate2::Compression;
use flate2::write::GzEncoder;
use rustc_hash::FxHashMap;

use crate::execute::tsc::compile::{Writer, write_str};
// PORT: the paths are port forms of Go strings (see
// `scanner_util::GO_STRING_MARKER`); the OS gets their Go bytes (`os_path`).
use crate::frontend::vfs::osvfs::{filepath_clean, os_path};

// Go: pprof/pprof.go:15 ProfileSession
// PORT: `cpu_file` is `None` after Go `p.cpuFile.Close()`. `cpu_profile`
// is the state of the Go `runtime/pprof` goroutine `profileWriter` (see
// `start_cpu_profile`).
pub struct ProfileSession {
    cpu_file_path: String,
    mem_file_path: String,
    cpu_file: Option<File>,
    log_writer: Writer,
    cpu_profile: Option<ProfileBuilder>,
}

// Go: pprof/pprof.go:23 BeginProfiling
// BeginProfiling starts CPU and memory profiling, writing the profiles to the specified directory.
// PORT: Go `panic(err)` panics with the Go error text.
#[must_use]
pub fn begin_profiling(profile_dir: &str, log_writer: Writer) -> ProfileSession {
    // Go: os.MkdirAll(profileDir, 0o755)
    if let Err(err) = DirBuilder::new()
        .recursive(true)
        .mode(0o755)
        .create(os_path(profile_dir))
    {
        panic!("mkdir {profile_dir}: {err}");
    }

    let pid = std::process::id();

    // Go: filepath.Join(profileDir, ...). `profileDir` is not empty.
    let cpu_profile_path = filepath_clean(&format!("{profile_dir}/{pid}-cpuprofile.pb.gz"));
    let mem_profile_path = filepath_clean(&format!("{profile_dir}/{pid}-memprofile.pb.gz"));
    let cpu_file = os_create(&cpu_profile_path);

    // Go: pprof.StartCPUProfile(cpuFile), then `panic(err)`.
    let cpu_profile = match start_cpu_profile() {
        Ok(cpu_profile) => cpu_profile,
        Err(err) => panic!("{err}"),
    };

    ProfileSession {
        cpu_file_path: cpu_profile_path,
        mem_file_path: mem_profile_path,
        cpu_file: Some(cpu_file),
        log_writer,
        cpu_profile: Some(cpu_profile),
    }
}

impl ProfileSession {
    // Go: pprof/pprof.go:49 Stop
    // PORT: only `Drop` calls it (Go `defer profileSession.Stop()`).
    fn stop(&mut self) {
        // Go: pprof.StopCPUProfile()
        if let (Some(cpu_profile), Some(cpu_file)) = (self.cpu_profile.take(), &self.cpu_file) {
            stop_cpu_profile(cpu_profile, cpu_file);
        }
        // Go: p.cpuFile.Close()
        self.cpu_file = None;

        if !self.mem_file_path.is_empty() {
            let mem_file = os_create(&self.mem_file_path);
            // Go: pprof.Lookup("allocs").WriteTo(memFile, 0), then `panic(err)`.
            if let Err(err) = write_alloc(&mem_file) {
                panic!("write {}: {err}", self.mem_file_path);
            }
            // Go: memFile.Close()
            drop(mem_file);
            write_str(
                &self.log_writer,
                &format!("Memory profile: {}\n", self.mem_file_path),
            );
        }

        write_str(
            &self.log_writer,
            &format!("CPU profile: {}\n", self.cpu_file_path),
        );
    }
}

// PORT: Go `defer profileSession.Stop()`. The callers keep the session
// in a local, so it stops when they return, and also when they panic,
// as a Go defer does.
impl Drop for ProfileSession {
    fn drop(&mut self) {
        self.stop();
    }
}

// Go: os.Create (O_RDWR|O_CREATE|O_TRUNC, 0o666), then `panic(err)`.
fn os_create(name: &str) -> File {
    match OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .open(os_path(name))
    {
        Ok(file) => file,
        Err(err) => panic!("open {name}: {err}"),
    }
}

// ---------------------------------------------------------------------
// Go standard library: runtime/pprof (go1.26.4)
// ---------------------------------------------------------------------

// Go: runtime/pprof/pprof.go:871 cpu (the `profiling` field)
// PORT: Go guards it with a mutex. The atomic swap does the same job.
static CPU_PROFILING: AtomicBool = AtomicBool::new(false);

// Go: runtime/mprof.go:880 MemProfileRate. tsgo does not change it.
const MEM_PROFILE_RATE: i64 = 512 * 1024;

// Go: runtime/pprof/pprof.go:888 StartCPUProfile
// PORT: Go starts the runtime sampler with `runtime.SetCPUProfileRate(hz)`
// and runs `profileWriter(w)` in a goroutine, which owns the profile
// builder and writes it to `w` when profiling stops. The port returns
// that builder, and `stop_cpu_profile` takes it back with `w`.
fn start_cpu_profile() -> Result<ProfileBuilder, &'static str> {
    // The runtime routines allow a variable profiling rate,
    // but in practice operating systems cannot trigger signals
    // at more than about 500 Hz, and our processing of the
    // signal is not cheap (mostly getting the stack trace).
    // 100 Hz is a reasonable choice: it is frequent enough to
    // produce useful data, rare enough not to bog down the
    // system, and a nice round number to make it easy to
    // convert sample counts to seconds. Instead of requiring
    // each client to specify the frequency, we hard code it.
    const HZ: i64 = 100;

    // Double-check.
    if CPU_PROFILING.swap(true, Ordering::SeqCst) {
        return Err("cpu profiling already in use");
    }

    // Go: pprof.go:922 profileWriter: b := newProfileBuilder(w)
    let mut b = ProfileBuilder::new();
    // Go: proto.go:278 addCPUData, for the header record that
    // `runtime.SetCPUProfileRate(hz)` writes first. The port has no other
    // record (see the module comment).
    // data[2] is sampling rate in Hz. Convert to sampling
    // period in nanoseconds.
    b.period = 1_000_000_000 / HZ;
    b.have_period = true;
    Ok(b)
}

// Go: runtime/pprof/pprof.go:950 StopCPUProfile
// StopCPUProfile stops the current CPU profile, if any.
// PORT: Go `<-cpu.done` waits for `profileWriter`, which reads the end
// of the profile, calls `b.build()` and ignores its error.
fn stop_cpu_profile(b: ProfileBuilder, w: &File) {
    if !CPU_PROFILING.swap(false, Ordering::SeqCst) {
        return;
    }
    let _ = b.build(w);
}

// Go: runtime/pprof/pprof.go:627 writeAlloc
// PORT: Go `pprof.Lookup("allocs").WriteTo(w, 0)` calls it with debug 0,
// so `writeHeapInternal` (pprof.go:631) calls `writeHeapProto` with the
// runtime memory profile records and `runtime.MemProfileRate`. The port
// has no records (see the module comment).
fn write_alloc(w: &File) -> io::Result<()> {
    write_heap_proto(w, MEM_PROFILE_RATE, "alloc_space")
}

// Go: runtime/pprof/protomem.go:16 writeHeapProto
// writeHeapProto writes the current heap profile in protobuf format to w.
// PORT: the record list `p` is always empty, so the loop over it is not
// ported.
fn write_heap_proto(w: &File, rate: i64, default_sample_type: &str) -> io::Result<()> {
    let mut b = ProfileBuilder::new();
    b.pb_value_type(TAG_PROFILE_PERIOD_TYPE, "space", "bytes");
    b.pb.int64_opt(TAG_PROFILE_PERIOD, rate);
    b.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "alloc_objects", "count");
    b.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "alloc_space", "bytes");
    b.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "inuse_objects", "count");
    b.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "inuse_space", "bytes");
    if !default_sample_type.is_empty() {
        let index = b.string_index(default_sample_type.as_bytes());
        b.pb.int64_opt(TAG_PROFILE_DEFAULT_SAMPLE_TYPE, index);
    }
    b.build(w)
}

// Go: runtime/pprof/proto.go:70 (the tags that a profile with no samples
// writes)
// message Profile
const TAG_PROFILE_SAMPLE_TYPE: u64 = 1; // repeated ValueType
const TAG_PROFILE_MAPPING: u64 = 3; // repeated Mapping
const TAG_PROFILE_STRING_TABLE: u64 = 6; // repeated string
const TAG_PROFILE_TIME_NANOS: u64 = 9; // int64
const TAG_PROFILE_DURATION_NANOS: u64 = 10; // int64
const TAG_PROFILE_PERIOD_TYPE: u64 = 11; // ValueType (really optional string???)
const TAG_PROFILE_PERIOD: u64 = 12; // int64
const TAG_PROFILE_DEFAULT_SAMPLE_TYPE: u64 = 14; // int64
// message ValueType
const TAG_VALUE_TYPE_TYPE: u64 = 1; // int64 (string table index)
const TAG_VALUE_TYPE_UNIT: u64 = 2; // int64 (string table index)
// message Mapping
const TAG_MAPPING_ID: u64 = 1; // uint64
const TAG_MAPPING_START: u64 = 2; // uint64
const TAG_MAPPING_LIMIT: u64 = 3; // uint64
const TAG_MAPPING_OFFSET: u64 = 4; // uint64
const TAG_MAPPING_FILENAME: u64 = 5; // int64 (string table index)
const TAG_MAPPING_BUILD_ID: u64 = 6; // int64 (string table index)

// Go: runtime/pprof/proto.go:27 profileBuilder
// A profileBuilder writes a profile incrementally from a
// stream of profile samples delivered by the runtime.
// PORT: only the fields that a profile with no samples uses. Go makes the
// gzip writer `zw` in `newProfileBuilder`. It writes nothing before its
// first `Write`, so `build` makes it. Go `time.Time` holds a wall and a
// monotonic reading: `start` is the wall reading for `UnixNano`, and
// `start_mono` the monotonic one for `Sub`. Go strings hold any bytes, so
// the string table holds bytes.
struct ProfileBuilder {
    start: SystemTime,
    start_mono: Instant,
    have_period: bool,
    period: i64,

    // encoding state
    pb: Protobuf,
    strings: Vec<Vec<u8>>,
    string_map: FxHashMap<Vec<u8>, i64>,
    mem: Vec<MemMap>,
}

// Go: runtime/pprof/proto.go:46 memMap
// PORT: `funcs` and `fake` serve locations, which a profile with no
// samples does not have.
struct MemMap {
    start: u64,       // Address at which the binary (or DLL) is loaded into memory.
    end: u64,         // The limit of the address range occupied by this mapping.
    offset: u64,      // Offset in the binary that corresponds to the first mapped address.
    file: Vec<u8>,    // The object this entry is loaded from.
    build_id: String, // A string that uniquely identifies a particular program version with high probability.
}

impl ProfileBuilder {
    // Go: runtime/pprof/proto.go:259 newProfileBuilder
    fn new() -> ProfileBuilder {
        let mut string_map = FxHashMap::default();
        string_map.insert(Vec::new(), 0);
        let mut b = ProfileBuilder {
            start: SystemTime::now(),
            start_mono: Instant::now(),
            have_period: false,
            period: 0,
            pb: Protobuf::default(),
            strings: vec![Vec::new()],
            string_map,
            mem: Vec::new(),
        };
        b.read_mapping();
        b
    }

    // Go: runtime/pprof/proto.go:133 stringIndex
    // stringIndex adds s to the string table if not already present
    // and returns the index of s in the string table.
    fn string_index(&mut self, s: &[u8]) -> i64 {
        if let Some(&id) = self.string_map.get(s) {
            return id;
        }
        let id = self.strings.len() as i64;
        self.strings.push(s.to_vec());
        self.string_map.insert(s.to_vec(), id);
        id
    }

    // Go: runtime/pprof/proto.go:152 pbValueType
    // pbValueType encodes a ValueType message to b.pb.
    fn pb_value_type(&mut self, tag: u64, typ: &str, unit: &str) {
        let start = self.pb.start_message();
        let typ = self.string_index(typ.as_bytes());
        self.pb.int64(TAG_VALUE_TYPE_TYPE, typ);
        let unit = self.string_index(unit.as_bytes());
        self.pb.int64(TAG_VALUE_TYPE_UNIT, unit);
        self.pb.end_message(tag, start);
    }

    // Go: runtime/pprof/proto.go:189 pbMapping
    // pbMapping encodes a Mapping message to b.pb.
    // PORT: Go writes `HasFunctions` only for a mapping whose locations
    // were all symbolized. A profile with no samples has no locations, so
    // `hasFuncs` is always false and not ported.
    fn pb_mapping(
        &mut self,
        tag: u64,
        id: u64,
        base: u64,
        limit: u64,
        offset: u64,
        file: &[u8],
        build_id: &str,
    ) {
        let start = self.pb.start_message();
        self.pb.uint64_opt(TAG_MAPPING_ID, id);
        self.pb.uint64_opt(TAG_MAPPING_START, base);
        self.pb.uint64_opt(TAG_MAPPING_LIMIT, limit);
        self.pb.uint64_opt(TAG_MAPPING_OFFSET, offset);
        let file = self.string_index(file);
        self.pb.int64_opt(TAG_MAPPING_FILENAME, file);
        let build_id = self.string_index(build_id.as_bytes());
        self.pb.int64_opt(TAG_MAPPING_BUILD_ID, build_id);
        self.pb.end_message(tag, start);
    }

    // Go: runtime/pprof/proto.go:348 build
    // build completes and returns the constructed profile.
    // PORT: Go writes a `Sample` message for each profiled stack between
    // the header and the mappings. The port has no samples.
    fn build(mut self, w: &File) -> io::Result<()> {
        // Go: b.end = time.Now()
        let end = Instant::now();

        self.pb
            .int64_opt(TAG_PROFILE_TIME_NANOS, unix_nano(self.start));
        if self.have_period {
            // must be CPU profile
            self.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "samples", "count");
            self.pb_value_type(TAG_PROFILE_SAMPLE_TYPE, "cpu", "nanoseconds");
            let duration = end.duration_since(self.start_mono).as_nanos() as i64;
            self.pb.int64_opt(TAG_PROFILE_DURATION_NANOS, duration);
            self.pb_value_type(TAG_PROFILE_PERIOD_TYPE, "cpu", "nanoseconds");
            self.pb.int64_opt(TAG_PROFILE_PERIOD, self.period);
        }

        let mem = std::mem::take(&mut self.mem);
        for (i, m) in mem.iter().enumerate() {
            self.pb_mapping(
                TAG_PROFILE_MAPPING,
                i as u64 + 1,
                m.start,
                m.end,
                m.offset,
                &m.file,
                &m.build_id,
            );
        }

        // TODO: Anything for tagProfile_DropFrames?
        // TODO: Anything for tagProfile_KeepFrames?

        self.pb.strings(TAG_PROFILE_STRING_TABLE, &self.strings);
        // Go: gzip.NewWriterLevel(w, gzip.BestSpeed) in newProfileBuilder.
        // Both write the gzip header with mtime 0, XFL 4 and OS 255.
        let mut zw = GzEncoder::new(w, Compression::fast());
        zw.write_all(&self.pb.data)?;
        // Go: b.zw.Close()
        zw.finish()?;
        Ok(())
    }

    // Go: runtime/pprof/proto_other.go:17 readMapping
    // readMapping reads /proc/self/maps and writes mappings to b.pb.
    // It saves the address ranges of the mappings in b.mem for use
    // when emitting locations.
    fn read_mapping(&mut self) {
        let data = std::fs::read("/proc/self/maps").unwrap_or_default();
        parse_proc_self_maps(&data, &mut |lo, hi, offset, file, build_id| {
            self.add_mapping_entry(lo, hi, offset, file, build_id);
        });
        if self.mem.is_empty() {
            // pprof expects a map entry, so fake one.
            self.add_mapping_entry(0, 0, 0, b"", String::new());
        }
    }

    // Go: runtime/pprof/proto.go:760 addMappingEntry
    // PORT: Go `addMapping` (proto.go:756) calls it with `fake` false.
    // The `fake` field is not ported (see `MemMap`).
    fn add_mapping_entry(&mut self, lo: u64, hi: u64, offset: u64, file: &[u8], build_id: String) {
        self.mem.push(MemMap {
            start: lo,
            end: hi,
            offset,
            file: file.to_vec(),
            build_id,
        });
    }
}

// Go: runtime/pprof/proto.go:665 parseProcSelfMaps
fn parse_proc_self_maps(
    mut data: &[u8],
    add_mapping: &mut dyn FnMut(u64, u64, u64, &[u8], String),
) {
    // $ cat /proc/self/maps
    // 00400000-0040b000 r-xp 00000000 fc:01 787766                             /bin/cat
    // 0060a000-0060b000 r--p 0000a000 fc:01 787766                             /bin/cat
    // 014ab000-014cc000 rw-p 00000000 00:00 0                                  [heap]
    // 7f7d7797c000-7f7d77b36000 r-xp 00000000 fc:01 1180226                    /lib/x86_64-linux-gnu/libc-2.19.so
    // 7f7d77d3c000-7f7d77d41000 rw-p 00000000 00:00 0
    // 7ffc34343000-7ffc34345000 r-xp 00000000 00:00 0                          [vdso]
    // ffffffffff600000-ffffffffff601000 r-xp 00000000 00:00 0                  [vsyscall]

    // next removes and returns the next field in the line.
    // It also removes from line any spaces following the field.
    fn next<'a>(line: &mut &'a [u8]) -> &'a [u8] {
        let (f, rest) = cut(*line, b' ');
        *line = trim_left_spaces(rest);
        f
    }

    while !data.is_empty() {
        let (mut line, rest) = cut(data, b'\n');
        data = rest;
        let addr = next(&mut line);
        let Some(dash) = memchr::memchr(b'-', addr) else {
            continue;
        };
        let (lo_str, hi_str) = (&addr[..dash], &addr[dash + 1..]);
        let Some(lo) = parse_uint_hex(lo_str) else {
            continue;
        };
        let Some(hi) = parse_uint_hex(hi_str) else {
            continue;
        };
        let perm = next(&mut line);
        if perm.len() < 4 || perm[2] != b'x' {
            // Only interested in executable mappings.
            continue;
        }
        let Some(offset) = parse_uint_hex(next(&mut line)) else {
            continue;
        };
        next(&mut line); // dev
        let inode = next(&mut line); // inode
        // PORT: Go `bytes.TrimLeft` in `next` returns nil for an empty
        // rest, so Go `line == nil` is an empty `line`.
        if line.is_empty() {
            continue;
        }
        let mut file = line;

        // Trim deleted file marker.
        const DELETED_STR: &[u8] = b" (deleted)";
        if file.ends_with(DELETED_STR) {
            file = &file[..file.len() - DELETED_STR.len()];
        }

        if inode == b"0" && file.is_empty() {
            // Huge-page text mappings list the initial fragment of
            // mapped but unpopulated memory as being inode 0.
            // Don't report that part.
            // But [vdso] and [vsyscall] are inode 0, so let non-empty file names through.
            continue;
        }

        // TODO: pprof's remapMappingIDs makes one adjustment:
        // 1. If there is an /anon_hugepage mapping first and it is
        // consecutive to a next mapping, drop the /anon_hugepage.
        // There's no indication why this is needed.
        // Let's try not doing this and see what breaks.
        // If we do need it, it would go here, before we
        // enter the mappings into b.mem in the first place.

        let build_id = elf_build_id(file).unwrap_or_default();
        add_mapping(lo, hi, offset, file, build_id);
    }
}

// Go: bytes.Cut(s, []byte{sep}). `after` is empty when `sep` is missing
// (Go returns nil, which the callers treat the same way).
fn cut(s: &[u8], sep: u8) -> (&[u8], &[u8]) {
    match memchr::memchr(sep, s) {
        Some(i) => (&s[..i], &s[i + 1..]),
        None => (s, &[]),
    }
}

// Go: bytes.TrimLeft(s, " ")
fn trim_left_spaces(s: &[u8]) -> &[u8] {
    let n = s.iter().take_while(|&&c| c == b' ').count();
    &s[n..]
}

// Go: strconv.ParseUint(s, 16, 64). Rust `from_str_radix` also takes a
// leading `+`, which Go rejects.
fn parse_uint_hex(s: &[u8]) -> Option<u64> {
    if s.first() == Some(&b'+') {
        return None;
    }
    u64::from_str_radix(std::str::from_utf8(s).ok()?, 16).ok()
}

// Go: time.Time.UnixNano
fn unix_nano(t: SystemTime) -> i64 {
    match t.duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_nanos() as i64,
        Err(err) => -(err.duration().as_nanos() as i64),
    }
}

// Go: runtime/pprof/elf.go:21 elfBuildID
// elfBuildID returns the GNU build ID of the named ELF binary,
// without introducing a dependency on debug/elf and its dependencies.
// PORT: Go returns an error that its only caller ignores. `None` is
// that error.
fn elf_build_id(file: &[u8]) -> Option<String> {
    let mut buf = [0u8; 256];
    let f = File::open(OsStr::from_bytes(file)).ok()?;

    read_at(&f, &mut buf[..64], 0)?;

    // ELF file begins with \x7F E L F.
    if buf[0] != 0x7F || buf[1] != b'E' || buf[2] != b'L' || buf[3] != b'F' {
        return None; // errBadELF
    }

    // Go: binary.LittleEndian (1) or binary.BigEndian (2). `uint` reads
    // the unsigned value of all bytes of `b`.
    let big_endian = match buf[5] {
        1 => false,       // little-endian
        2 => true,        // big-endian
        _ => return None, // errBadELF
    };
    let uint = move |b: &[u8]| -> u64 {
        let mut x = 0u64;
        if big_endian {
            for &c in b {
                x = x << 8 | u64::from(c);
            }
        } else {
            for &c in b.iter().rev() {
                x = x << 8 | u64::from(c);
            }
        }
        x
    };

    let (shnum, shoff, shentsize): (i64, i64, i64) = match buf[4] {
        1 => {
            // 32-bit file header
            let shoff = uint(&buf[32..36]) as i64;
            let shentsize = uint(&buf[46..48]) as i64;
            if shentsize != 40 {
                return None; // errBadELF
            }
            (uint(&buf[48..50]) as i64, shoff, shentsize)
        }
        2 => {
            // 64-bit file header
            let shoff = uint(&buf[40..48]) as i64;
            let shentsize = uint(&buf[58..60]) as i64;
            if shentsize != 64 {
                return None; // errBadELF
            }
            (uint(&buf[60..62]) as i64, shoff, shentsize)
        }
        _ => return None, // errBadELF
    };

    for i in 0..shnum {
        read_at(
            &f,
            &mut buf[..shentsize as usize],
            shoff.wrapping_add(i.wrapping_mul(shentsize)),
        )?;
        if uint(&buf[4..8]) != 7 {
            // SHT_NOTE
            continue;
        }
        let (mut off, mut size) = if shentsize == 40 {
            // 32-bit section header
            (uint(&buf[16..20]) as i64, uint(&buf[20..24]) as i64)
        } else {
            // 64-bit section header
            (uint(&buf[24..32]) as i64, uint(&buf[32..40]) as i64)
        };
        size = size.wrapping_add(off);
        while off < size {
            // room for header + name GNU\x00
            read_at(&f, &mut buf[..16], off)?;
            let name_size = uint(&buf[0..4]) as i64;
            let desc_size = uint(&buf[4..8]) as i64;
            let note_type = uint(&buf[8..12]);
            let desc_off = off.wrapping_add(12 + ((name_size + 3) & !3));
            off = desc_off.wrapping_add((desc_size + 3) & !3);
            if name_size != 4 || note_type != 3 || &buf[12..16] != b"GNU\x00" {
                // want name GNU\x00 type 3 (NT_GNU_BUILD_ID)
                continue;
            }
            if desc_size > buf.len() as i64 {
                return None; // errBadELF
            }
            read_at(&f, &mut buf[..desc_size as usize], desc_off)?;
            // Go: fmt.Sprintf("%x", buf[:descSize])
            let mut id = String::with_capacity(desc_size as usize * 2);
            for c in &buf[..desc_size as usize] {
                id.push_str(&format!("{c:02x}"));
            }
            return Some(id);
        }
    }
    None // errNoBuildID
}

// Go: (*os.File).ReadAt, which fails on a negative offset and on a short
// read.
fn read_at(f: &File, buf: &mut [u8], off: i64) -> Option<()> {
    f.read_exact_at(buf, u64::try_from(off).ok()?).ok()
}

// Go: runtime/pprof/protobuf.go:8 protobuf
// A protobuf is a simple protocol buffer encoder.
// PORT: Go `tmp` holds the length bytes that `endMessage` moves, and
// `nest` serves `profileBuilder.flush`. `end_message` rotates the slice
// instead, and `flush` serves samples and locations, which the port does
// not write. So neither field is ported.
#[derive(Default)]
struct Protobuf {
    data: Vec<u8>,
}

impl Protobuf {
    // Go: runtime/pprof/protobuf.go:14 varint
    fn varint(&mut self, mut x: u64) {
        while x >= 128 {
            self.data.push(x as u8 | 0x80);
            x >>= 7;
        }
        self.data.push(x as u8);
    }

    // Go: runtime/pprof/protobuf.go:22 length
    fn length(&mut self, tag: u64, len: usize) {
        self.varint(tag << 3 | 2);
        self.varint(len as u64);
    }

    // Go: runtime/pprof/protobuf.go:27 uint64
    fn uint64(&mut self, tag: u64, x: u64) {
        // append varint to b.data
        self.varint(tag << 3);
        self.varint(x);
    }

    // Go: runtime/pprof/protobuf.go:53 uint64Opt
    fn uint64_opt(&mut self, tag: u64, x: u64) {
        if x == 0 {
            return;
        }
        self.uint64(tag, x);
    }

    // Go: runtime/pprof/protobuf.go:60 int64
    fn int64(&mut self, tag: u64, x: i64) {
        self.uint64(tag, x as u64);
    }

    // Go: runtime/pprof/protobuf.go:65 int64Opt
    fn int64_opt(&mut self, tag: u64, x: i64) {
        if x == 0 {
            return;
        }
        self.int64(tag, x);
    }

    // Go: runtime/pprof/protobuf.go:92 string
    fn string(&mut self, tag: u64, x: &[u8]) {
        self.length(tag, x.len());
        self.data.extend_from_slice(x);
    }

    // Go: runtime/pprof/protobuf.go:97 strings
    fn strings(&mut self, tag: u64, x: &[Vec<u8>]) {
        for s in x {
            self.string(tag, s);
        }
    }

    // Go: runtime/pprof/protobuf.go:127 startMessage
    fn start_message(&mut self) -> usize {
        self.data.len()
    }

    // Go: runtime/pprof/protobuf.go:132 endMessage
    // PORT: Go appends the length, then moves its bytes in front of the
    // message with `tmp`. `rotate_right` moves them the same way.
    fn end_message(&mut self, tag: u64, start: usize) {
        let n1 = start;
        let n2 = self.data.len();
        self.length(tag, n2 - n1);
        let n3 = self.data.len();
        self.data[n1..].rotate_right(n3 - n2);
    }
}
