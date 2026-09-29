//! The subset of Go `golang.org/x/sys/unix` (v0.46.0, darwin and the BSDs)
//! that fswatch uses there: the kqueue backend (kqueue.go) and the directory
//! walk (walkdir_unix.go). There is no Go file for this module in
//! typescript-go. It is `fswatch::unix` on darwin, FreeBSD, OpenBSD, NetBSD
//! and DragonFly; unix.rs is the Linux one.
//!
//! PORT: D-W1 allows a safe syscall crate. kqueue(2) and kevent(2) go
//! through `nix::sys::event` (safe API: `Kqueue::kevent`). The pipe, open,
//! openat, write, close, fstat and directory reads go through `rustix` (safe
//! API) or `std`. No `libc` calls, no `unsafe`. Every syscall keeps its Go
//! name, parameters and result. The open(2) flags, the kevent filters and
//! flags are the target's values (from rustix and nix); the const asserts
//! below check them against Go's darwin values (zerrors_darwin_amd64.go and
//! zerrors_darwin_arm64.go agree on these).
//!
//! PORT: Go passes raw fd numbers. As in unix.rs, every fd this shim opens
//! stays in `FDS` under its number until `close`.

use crate::fswatch::prelude::*;
pub use crate::fswatch::syscall::*;
use crate::gostd::errors;
use nix::sys::event::{EvFlags, EventFilter, FilterFlag, KEvent, Kqueue};
use rustix::fs::OFlags;
use std::os::fd::{AsFd, AsRawFd};
use std::sync::{Arc, LazyLock, Mutex};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

// open(2) flags (Go int), the target's values.
pub const O_RDONLY: i32 = OFlags::RDONLY.bits() as i32;
pub const O_CLOEXEC: i32 = OFlags::CLOEXEC.bits() as i32;
pub const O_NONBLOCK: i32 = OFlags::NONBLOCK.bits() as i32;
pub const O_DIRECTORY: i32 = OFlags::DIRECTORY.bits() as i32;
pub const O_NOCTTY: i32 = OFlags::NOCTTY.bits() as i32;
pub const O_NOFOLLOW: i32 = OFlags::NOFOLLOW.bits() as i32;

// Dirent.Type values (Go uint8).
pub const DT_UNKNOWN: u8 = 0x0;
pub const DT_DIR: u8 = 0x4;

// Stat_t.Mode bits (Go uint16 on darwin, uint16 or uint32 on the BSDs).
pub const S_IFMT: u32 = 0xf000;
pub const S_IFDIR: u32 = 0x4000;

// kevent filters (Go int16) and flags (Go uint16), the target's values.
pub const EVFILT_READ: i16 = EventFilter::EVFILT_READ as i16;
pub const EVFILT_VNODE: i16 = EventFilter::EVFILT_VNODE as i16;
pub const EV_ADD: u16 = EvFlags::EV_ADD.bits() as u16;
pub const EV_ENABLE: u16 = EvFlags::EV_ENABLE.bits() as u16;
pub const EV_CLEAR: u16 = EvFlags::EV_CLEAR.bits() as u16;
pub const EV_ERROR: u16 = EvFlags::EV_ERROR.bits() as u16;

// EVFILT_VNODE fflags (Go uint32).
pub const NOTE_DELETE: u32 = FilterFlag::NOTE_DELETE.bits();
pub const NOTE_WRITE: u32 = FilterFlag::NOTE_WRITE.bits();
pub const NOTE_EXTEND: u32 = FilterFlag::NOTE_EXTEND.bits();
pub const NOTE_ATTRIB: u32 = FilterFlag::NOTE_ATTRIB.bits();
pub const NOTE_RENAME: u32 = FilterFlag::NOTE_RENAME.bits();
pub const NOTE_REVOKE: u32 = FilterFlag::NOTE_REVOKE.bits();

// The values above against Go's darwin values (x/sys v0.46.0
// zerrors_darwin_amd64.go and zerrors_darwin_arm64.go).
#[cfg(target_vendor = "apple")]
const _: () = assert!(
    O_RDONLY == 0x0
        && O_CLOEXEC == 0x1000000
        && O_NONBLOCK == 0x4
        && O_DIRECTORY == 0x100000
        && O_NOCTTY == 0x20000
        && O_NOFOLLOW == 0x100
        && EVFILT_READ == -0x1
        && EVFILT_VNODE == -0x4
        && EV_ADD == 0x1
        && EV_ENABLE == 0x4
        && EV_CLEAR == 0x20
        && EV_ERROR == 0x4000
        && NOTE_DELETE == 0x1
        && NOTE_WRITE == 0x2
        && NOTE_EXTEND == 0x4
        && NOTE_ATTRIB == 0x8
        && NOTE_RENAME == 0x20
        && NOTE_REVOKE == 0x40
);

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

// Go: ztypes_darwin_amd64.go Timespec
#[derive(Clone, Copy, Debug, Default)]
pub struct Timespec {
    pub sec: i64,
    pub nsec: i64,
}

// Go: ztypes_darwin_amd64.go Stat_t
// PORT: the fields fswatch reads (Dev, Ino, Mode), filled from `std`
// metadata, not cast. The types are wide enough for every BSD (Go darwin
// has Dev int32 and Mode uint16).
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Stat_t {
    pub dev: u64,
    pub ino: u64,
    pub mode: u32,
}

// Go: ztypes_darwin_amd64.go Kevent_t
// PORT: Go's per-OS field types are the darwin ones. `udata` is an integer
// (nix `KEvent::udata`); fswatch never sets it.
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Kevent_t {
    pub ident: u64,
    pub filter: i16,
    pub flags: u16,
    pub fflags: u32,
    pub data: i64,
    pub udata: i64,
}

// Go: syscall_bsd.go SetKevent
/// SetKevent converts fd, mode and flags to the Ident, Filter and Flags of
/// k.
pub fn set_kevent(k: &mut Kevent_t, fd: i32, mode: i16, flags: u16) {
    k.ident = fd as u64;
    k.filter = mode;
    k.flags = flags;
}

// PORT: nix wants a typed filter. fswatch uses these two.
fn event_filter(filter: i16) -> Result<EventFilter, GoError> {
    match filter {
        EVFILT_READ => Ok(EventFilter::EVFILT_READ),
        EVFILT_VNODE => Ok(EventFilter::EVFILT_VNODE),
        _ => Err(errors::from_value(EINVAL)),
    }
}

impl Kevent_t {
    fn to_nix(self) -> Result<KEvent, GoError> {
        Ok(KEvent::new(
            self.ident as usize,
            event_filter(self.filter)?,
            EvFlags::from_bits_retain(self.flags as _),
            FilterFlag::from_bits_retain(self.fflags as _),
            self.data as _,
            self.udata as _,
        ))
    }

    fn from_nix(ev: &KEvent) -> Kevent_t {
        Kevent_t {
            ident: ev.ident() as u64,
            // A filter nix does not name is not one fswatch registered.
            filter: ev.filter().map_or(0, |f| f as i16),
            flags: ev.flags().bits() as u16,
            fflags: ev.fflags().bits() as u32,
            data: ev.data() as i64,
            udata: ev.udata() as i64,
        }
    }
}

// Go: ztypes_linux_amd64.go Dirent (the record the shim writes)
/// PORT: `read_dirent` writes one record layout on every target, the Linux
/// `linux_dirent64` header (ino, off, reclen, type, name), so walkdir_unix.rs
/// reads darwin and BSD entries as it reads Linux ones. Go reads the kernel
/// records of each OS (walkdir_dirent_{darwin,fileno,noreclen}.go); the
/// entries are the same.
#[derive(Clone, Copy, Debug, Default)]
pub struct Dirent {
    pub ino: u64,
    pub off: i64,
    pub reclen: u16,
    pub type_: u8,
}

/// The name offset of the record `read_dirent` writes.
pub const DIRENT_NAME_OFFSET: usize = 19;

impl Dirent {
    /// PORT: reads the native-endian header fields; bytes past the end of
    /// `b` read as zero (a zero `reclen` stops the walk).
    pub fn from_ne_bytes(b: &[u8]) -> Dirent {
        let mut r = [0u8; DIRENT_NAME_OFFSET];
        let n = b.len().min(DIRENT_NAME_OFFSET);
        r[..n].copy_from_slice(&b[..n]);
        Dirent {
            ino: u64::from_ne_bytes([r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]]),
            off: i64::from_ne_bytes([r[8], r[9], r[10], r[11], r[12], r[13], r[14], r[15]]),
            reclen: u16::from_ne_bytes([r[16], r[17]]),
            type_: r[18],
        }
    }
}

// ---------------------------------------------------------------------------
// Syscalls
// ---------------------------------------------------------------------------

// PORT: an fd in `FDS`. A kqueue keeps its `nix` `Kqueue`, because kevent(2)
// is the `Kqueue::kevent` method. A directory that `read_dirent` reads also
// keeps its rustix `Dir` (the readdir position) and the entry that did not
// fit the last buffer.
enum ShimFd {
    Owned(std::os::fd::OwnedFd),
    Kqueue(Kqueue),
}

impl AsFd for ShimFd {
    fn as_fd(&self) -> std::os::fd::BorrowedFd<'_> {
        match self {
            ShimFd::Owned(fd) => fd.as_fd(),
            ShimFd::Kqueue(kq) => kq.as_fd(),
        }
    }
}

struct DirState {
    dir: rustix::fs::Dir,
    pending: Option<Vec<u8>>,
}

static FDS: LazyLock<Mutex<FxHashMap<i32, Arc<ShimFd>>>> = LazyLock::new(Default::default);
static DIRS: LazyLock<Mutex<FxHashMap<i32, DirState>>> = LazyLock::new(Default::default);

fn register_fd(fd: ShimFd) -> i32 {
    let n = fd.as_fd().as_raw_fd();
    FDS.lock().unwrap().insert(n, Arc::new(fd));
    n
}

fn lookup_fd(fd: i32) -> Result<Arc<ShimFd>, GoError> {
    FDS.lock()
        .unwrap()
        .get(&fd)
        .cloned()
        .ok_or_else(|| errors::from_value(EBADF))
}

fn errno_error(e: rustix::io::Errno) -> GoError {
    errors::from_value(Errno(e.raw_os_error() as usize))
}

fn nix_error(e: nix::errno::Errno) -> GoError {
    errors::from_value(Errno(e as i32 as usize))
}

fn io_error(e: &std::io::Error) -> GoError {
    errors::from_value(Errno(e.raw_os_error().unwrap_or(EINVAL.0 as i32) as usize))
}

// Go: syscall_darwin.go Pipe
pub fn pipe(p: &mut [i32]) -> Result<(), GoError> {
    if p.len() != 2 {
        return Err(errors::from_value(EINVAL));
    }
    let (r, w) = rustix::pipe::pipe().map_err(errno_error)?;
    p[0] = register_fd(ShimFd::Owned(r));
    p[1] = register_fd(ShimFd::Owned(w));
    Ok(())
}

// Go: syscall_unix.go Write
pub fn write(fd: i32, p: &[u8]) -> Result<i32, GoError> {
    let f = lookup_fd(fd)?;
    let n = rustix::io::write(&*f, p).map_err(errno_error)?;
    Ok(n as i32)
}

// Go: zsyscall_darwin_amd64.go Close
pub fn close(fd: i32) -> Result<(), GoError> {
    DIRS.lock().unwrap().remove(&fd);
    match FDS.lock().unwrap().remove(&fd) {
        Some(_) => Ok(()),
        None => Err(errors::from_value(EBADF)),
    }
}

// Go: syscall_darwin.go Open
pub fn open(path: &str, mode: i32, perm: u32) -> Result<i32, GoError> {
    let fd = rustix::fs::open(
        path,
        OFlags::from_bits_retain(mode as _),
        rustix::fs::Mode::from_bits_retain(perm as _),
    )
    .map_err(errno_error)?;
    Ok(register_fd(ShimFd::Owned(fd)))
}

// Go: zsyscall_darwin_amd64.go Openat
pub fn openat(dirfd: i32, path: &str, flags: i32, mode: u32) -> Result<i32, GoError> {
    let dir = lookup_fd(dirfd)?;
    let fd = rustix::fs::openat(
        &*dir,
        path,
        OFlags::from_bits_retain(flags as _),
        rustix::fs::Mode::from_bits_retain(mode as _),
    )
    .map_err(errno_error)?;
    Ok(register_fd(ShimFd::Owned(fd)))
}

// Go: syscall_darwin.go ReadDirent (getdirentries)
/// PORT: the entries come from a rustix `Dir` (readdir) kept for `fd` until
/// `close`, and are written to `buf` in the record layout of `Dirent`. An
/// entry that does not fit waits for the next call; 0 means the end.
pub fn read_dirent(fd: i32, buf: &mut [u8]) -> Result<i32, GoError> {
    let mut dirs = DIRS.lock().unwrap();
    let state = match dirs.entry(fd) {
        std::collections::hash_map::Entry::Occupied(e) => e.into_mut(),
        std::collections::hash_map::Entry::Vacant(e) => {
            let f = lookup_fd(fd)?;
            let dir = rustix::fs::Dir::read_from(&*f).map_err(errno_error)?;
            e.insert(DirState { dir, pending: None })
        }
    };
    let mut n = 0usize;
    loop {
        let rec = match state.pending.take() {
            Some(rec) => rec,
            None => match state.dir.read() {
                None => break,
                Some(ent) => dirent_record(&ent.map_err(errno_error)?),
            },
        };
        if n + rec.len() > buf.len() {
            if n == 0 {
                return Err(errors::from_value(EINVAL));
            }
            state.pending = Some(rec);
            break;
        }
        buf[n..n + rec.len()].copy_from_slice(&rec);
        n += rec.len();
    }
    Ok(n as i32)
}

// PORT: one entry in the record layout of `Dirent`.
fn dirent_record(ent: &rustix::fs::DirEntry) -> Vec<u8> {
    let name = ent.file_name().to_bytes();
    let reclen = (DIRENT_NAME_OFFSET + name.len() + 1 + 7) & !7;
    let mut rec = vec![0u8; reclen];
    rec[0..8].copy_from_slice(&ent.ino().to_ne_bytes());
    rec[16..18].copy_from_slice(&(reclen as u16).to_ne_bytes());
    rec[18] = dirent_type(ent.file_type());
    rec[DIRENT_NAME_OFFSET..DIRENT_NAME_OFFSET + name.len()].copy_from_slice(name);
    rec
}

// PORT: the `d_type` byte that rustix turned into a `FileType` (the DT_*
// values are the same on darwin and the BSDs).
fn dirent_type(t: rustix::fs::FileType) -> u8 {
    use rustix::fs::FileType;
    match t {
        FileType::Fifo => 0x1,
        FileType::CharacterDevice => 0x2,
        FileType::Directory => DT_DIR,
        FileType::BlockDevice => 0x6,
        FileType::RegularFile => 0x8,
        FileType::Symlink => 0xa,
        FileType::Socket => 0xc,
        _ => DT_UNKNOWN,
    }
}

// PORT: the Stat_t fields fswatch reads, from `std` metadata.
fn stat_from(m: &std::fs::Metadata) -> Stat_t {
    use std::os::unix::fs::MetadataExt;
    Stat_t {
        dev: m.dev(),
        ino: m.ino(),
        mode: m.mode(),
    }
}

// Go: syscall_darwin.go Lstat
/// PORT: `std::fs::symlink_metadata` makes the same lstat(2) call.
pub fn lstat(path: &str, stat: &mut Stat_t) -> Result<(), GoError> {
    let m = std::fs::symlink_metadata(path).map_err(|e| io_error(&e))?;
    *stat = stat_from(&m);
    Ok(())
}

// Go: syscall_darwin.go Fstat
/// PORT: rustix `fstat` makes the same fstat(2) call.
pub fn fstat(fd: i32, stat: &mut Stat_t) -> Result<(), GoError> {
    let f = lookup_fd(fd)?;
    let st = rustix::fs::fstat(&*f).map_err(errno_error)?;
    *stat = Stat_t {
        dev: st.st_dev as u64,
        ino: st.st_ino as u64,
        mode: st.st_mode as u32,
    };
    Ok(())
}

// Go: zsyscall_darwin_amd64.go Kqueue
pub fn kqueue() -> Result<i32, GoError> {
    let kq = Kqueue::new().map_err(nix_error)?;
    Ok(register_fd(ShimFd::Kqueue(kq)))
}

// Go: syscall_bsd.go Kevent
/// PORT: `nix` `Kqueue::kevent` makes the same kevent(2) call. An fd that is
/// not a kqueue fails with EBADF, as in the kernel.
pub fn kevent(
    kq: i32,
    changes: &[Kevent_t],
    events: &mut [Kevent_t],
    timeout: Option<&Timespec>,
) -> Result<i32, GoError> {
    let f = lookup_fd(kq)?;
    let ShimFd::Kqueue(kq) = &*f else {
        return Err(errors::from_value(EBADF));
    };
    let changelist = changes
        .iter()
        .map(|c| c.to_nix())
        .collect::<Result<Vec<_>, _>>()?;
    let zero = KEvent::new(
        0,
        EventFilter::EVFILT_READ,
        EvFlags::empty(),
        FilterFlag::empty(),
        0,
        0,
    );
    let mut eventlist = vec![zero; events.len()];
    let timeout = timeout.map(|t| *nix::sys::time::TimeSpec::new(t.sec as _, t.nsec as _).as_ref());
    let n = kq
        .kevent(&changelist, &mut eventlist, timeout)
        .map_err(nix_error)?;
    for (e, ev) in events.iter_mut().zip(&eventlist[..n]) {
        *e = Kevent_t::from_nix(ev);
    }
    Ok(n as i32)
}
