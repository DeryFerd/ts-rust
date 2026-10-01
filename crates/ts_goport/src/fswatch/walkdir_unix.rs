//! Go: internal/fswatch/walkdir_unix.go and walkdir_dirent_linux.go (the
//! getdents directory walk used by the Linux backends and, on darwin and the
//! BSDs, by the kqueue backend).
//!
//! PORT: the syscalls go through the `unix` shim (rustix, D-W1). Dirent
//! records are read with `unix::Dirent::from_ne_bytes`
//! instead of Go's `unsafe.Pointer` cast. On darwin and the BSDs the shim
//! (unix_bsd.rs) writes the entries in the Linux record layout, so the
//! Linux helpers below serve there too; the darwin and BSD dirent helpers
//! (walkdir_dirent_{darwin,fileno,noreclen}.go) are not needed.

use crate::fswatch::prelude::*;

use crate::frontend::vfs::osvfs::go_string_from_os;
use crate::fswatch::unix;
use crate::gostd::errors;
use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;

// Go: walkdir_unix.go:14 walkState
/// walkState carries state shared across the whole walk so we only
/// allocate one read buffer per top-level walkDir, not one per directory.
pub struct WalkState {
    pub buf: Vec<u8>,
}

// Go: walkdir_unix.go:21 walkDir
/// walkDir walks dir, optionally recursively, invoking fn for each entry.
/// On Linux/BSDs it uses getdents/getdirentries directly so the d_type
/// in each record drives the isDir flag without a stat.
pub fn walk_dir(
    dir: &str,
    recursive: bool,
    fn_: Option<&mut dyn FnMut(&str, bool) -> Result<(), GoError>>,
) -> Result<(), GoError> {
    const OPEN_FLAGS: i32 = unix::O_RDONLY
        | unix::O_CLOEXEC
        | unix::O_DIRECTORY
        | unix::O_NOCTTY
        | unix::O_NONBLOCK
        | unix::O_NOFOLLOW;
    let fd = match unix::open(dir, OPEN_FLAGS, 0) {
        Ok(fd) => fd,
        Err(err) => {
            // Fall back to a path-based open when O_DIRECTORY rejects a
            // non-directory: walkDir's contract is to return ENOTDIR.
            if errors::is(&err, &errors::from_value(unix::ENOTDIR)) {
                return Err(errors::from_value(unix::ENOTDIR));
            }
            return Err(err);
        }
    };
    // PORT: Go `defer unix.Close(fd)`: an explicit call after the walk.

    let mut st = WalkState {
        buf: vec![0u8; 8192],
    };
    let result = iterate_dir(&mut st, fd, dir, recursive, fn_);
    let _ = unix::close(fd);
    result
}

// Go: walkdir_unix.go:44 iterateDir
/// iterateDir reads fd's entries, invokes fn for the dir and each entry,
/// and recurses into subdirectories via openat(fd, name). fd is owned by
/// the caller; iterateDir does not close it. Sharing fd as the openat
/// anchor for children avoids reopening the parent path once for the
/// listing and again for each child.
///
/// PORT: the trait object carries its own lifetime `'f` so the recursive
/// call can reborrow `fn_` for one iteration only (Go passes `fn` by value).
pub fn iterate_dir<'f>(
    st: &mut WalkState,
    fd: i32,
    dirname: &str,
    recursive: bool,
    mut fn_: Option<&mut (dyn FnMut(&str, bool) -> Result<(), GoError> + 'f)>,
) -> Result<(), GoError> {
    if let Some(f) = fn_.as_deref_mut() {
        f(dirname, true)?;
    }
    let entries = read_dir_entries(fd, &mut st.buf)?;

    const CHILD_OPEN_FLAGS: i32 = unix::O_RDONLY
        | unix::O_CLOEXEC
        | unix::O_DIRECTORY
        | unix::O_NOCTTY
        | unix::O_NONBLOCK
        | unix::O_NOFOLLOW;
    for ent in &entries {
        let full_path = format!("{dirname}/{}", ent.name);
        let mut is_dir = ent.typ == unix::DT_DIR;
        if ent.typ == unix::DT_UNKNOWN {
            let mut attrib = unix::Stat_t::default();
            if unix::lstat(&full_path, &mut attrib).is_err() {
                continue;
            }
            is_dir = (attrib.mode & unix::S_IFMT) == unix::S_IFDIR;
        }
        if !is_dir {
            if let Some(f) = fn_.as_deref_mut() {
                f(&full_path, false)?;
            }
            continue;
        }
        if !recursive {
            if let Some(f) = fn_.as_deref_mut() {
                f(&full_path, true)?;
            }
            continue;
        }
        let child_fd = match unix::openat(fd, &ent.name, CHILD_OPEN_FLAGS, 0) {
            Ok(child_fd) => child_fd,
            Err(err) => {
                if errors::is(&err, &errors::from_value(unix::EACCES))
                    || errors::is(&err, &errors::from_value(unix::ENOTDIR))
                    || errors::is(&err, &errors::from_value(unix::ENOENT))
                {
                    continue;
                }
                return Err(err);
            }
        };
        let err = iterate_dir(st, child_fd, &full_path, recursive, fn_.as_deref_mut());
        let _ = unix::close(child_fd);
        err?;
    }
    Ok(())
}

// Go: walkdir_unix.go:99 unixDirent
#[derive(Clone, Debug)]
pub struct UnixDirent {
    pub name: String,
    pub typ: u8,
}

// Go: walkdir_unix.go:108 readDirEntries
/// readDirEntries reads every entry on fd via getdents/getdirentries,
/// extracting d_type so callers can skip per-entry lstat on filesystems
/// that support it. The supplied buf is reused for every getdents
/// syscall in the loop and may be reused across calls.
pub fn read_dir_entries(fd: i32, buf: &mut [u8]) -> Result<Vec<UnixDirent>, GoError> {
    let mut entries: Vec<UnixDirent> = Vec::new();
    loop {
        let n = unix::read_dirent(fd, buf)?;
        if n <= 0 {
            break;
        }
        let mut data = &buf[..n as usize];
        while !data.is_empty() {
            let dirent = unix::Dirent::from_ne_bytes(data);
            let reclen = reclen_of(&dirent);
            if reclen == 0 || reclen as usize > data.len() {
                break;
            }
            if ino_of(&dirent) == 0 {
                data = &data[reclen as usize..];
                continue;
            }
            let name_off = unix::DIRENT_NAME_OFFSET;
            let mut name_bytes = &data[name_off..reclen as usize];
            if let Some(i) = name_bytes.iter().position(|&b| b == 0) {
                name_bytes = &name_bytes[..i];
            }
            // PORT: Go names are bytes. The port form keeps the bytes of a
            // non-UTF-8 name (`go_string_from_os`), and the `unix` shim
            // passes them back to the OS.
            let name = go_string_from_os(OsStr::from_bytes(name_bytes));
            if name != "." && name != ".." {
                entries.push(UnixDirent {
                    name,
                    typ: dirent.type_,
                });
            }
            data = &data[reclen as usize..];
        }
    }
    Ok(entries)
}

// Go: walkdir_dirent_linux.go:7 reclenOf
pub fn reclen_of(d: &unix::Dirent) -> u16 {
    d.reclen
}

// Go: walkdir_dirent_linux.go:8 inoOf
pub fn ino_of(d: &unix::Dirent) -> u64 {
    d.ino
}
