//! Go: internal/nativepath: realpath_linux.go, realpath_other.go,
//! realpath_windows.go, eintr_unix.go, symlink_other.go and
//! symlink_windows.go. Off Windows also the Go standard library
//! `filepath.EvalSymlinks` that two of them call.
//!
//! OS path helpers that osvfs and fswatch share. Paths are OS paths in the
//! port form (see `vfs::osvfs::os_path`).

use crate::frontend::vfs::FsError;
#[cfg(not(windows))]
use crate::frontend::vfs::osvfs::filepath_clean;
use crate::frontend::vfs::osvfs::{go_string_from_os, os_path};
use std::io;
#[cfg(target_os = "linux")]
use std::os::fd::AsRawFd;
#[cfg(target_os = "linux")]
use std::os::unix::fs::OpenOptionsExt;
use std::sync::OnceLock;

// Go: realpath_linux.go:32 _procSelfFD
const PROC_SELF_FD: &str = "/proc/self/fd/";

// PORT: Linux `O_PATH`, the value of the target (rustix).
#[cfg(target_os = "linux")]
const O_PATH: i32 = rustix::fs::OFlags::PATH.bits() as i32;

// Go: realpath_linux.go:34 hasProcSelfFD
fn has_proc_self_fd() -> bool {
    static VALUE: OnceLock<bool> = OnceLock::new();
    *VALUE.get_or_init(|| std::fs::metadata(PROC_SELF_FD).is_ok())
}

// Go: realpath_linux.go:39 Realpath
// On Linux, we use the O_PATH + /proc/self/fd trick to resolve the canonical
// path in O(1) syscalls (open + readlink + close) instead of Go's
// filepath.EvalSymlinks which does an lstat per path component — O(depth).
//
// Falls back to filepath.EvalSymlinks if /proc is not available (e.g. containers
// or chroots without procfs mounted).
#[cfg(target_os = "linux")]
pub fn realpath(path: &str) -> Result<String, FsError> {
    if !has_proc_self_fd() {
        return eval_symlinks(path);
    }

    // PORT: Rust std always adds O_CLOEXEC. The file is closed when it drops
    // (Go `defer unix.Close(fd)`).
    let file = ignoring_eintr(|| {
        std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(O_PATH)
            .open(os_path(path))
    })
    .map_err(|err| FsError::path("open", path, err))?;

    let proc_path = format!("{}{}", PROC_SELF_FD, file.as_raw_fd());

    // PORT: Go grows its readlink buffer until the target fits.
    // `std::fs::read_link` does the same internally.
    let target = ignoring_eintr(|| std::fs::read_link(&proc_path))
        .map_err(|err| FsError::path("readlink", path, err))?;
    Ok(go_string_from_os(target))
}

// Go: realpath_other.go:7 Realpath
// PORT: every target but Linux and Windows (macOS, the BSDs, wasm).
#[cfg(not(any(target_os = "linux", windows)))]
pub fn realpath(path: &str) -> Result<String, FsError> {
    eval_symlinks(path)
}

// Go: path/filepath/symlink.go:16 walkSymlinks (go1.27.1), which
// `filepath.EvalSymlinks` calls on unix (symlink_unix.go:9 evalSymlinks).
/// `path` with each symlink part replaced by the link text, then cleaned.
/// Every other part keeps the caller's spelling: the walk never reads a
/// stored name. libc `realpath(3)` on macOS gives the on-disk case of every
/// part instead, so a project path typed in another case gave a file reached
/// through a workspace link a second spelling (issue #50).
///
/// PORT: the unix form. There is no volume name and "." is never a link
/// (Go `isWindowsDot`). Go `os.Lstat` and `os.Readlink` are
/// `std::fs::symlink_metadata` and `std::fs::read_link`. Go returns a bare
/// `syscall.ENOTDIR`; the port gives its text, which no caller reads.
#[cfg(not(windows))]
fn eval_symlinks(path: &str) -> Result<String, FsError> {
    let mut path = path.to_string();
    let mut vol_len = 0;
    if vol_len < path.len() && path.as_bytes()[vol_len] == b'/' {
        vol_len += 1;
    }
    let mut vol = path[..vol_len].to_string();
    let mut dest = vol.clone();
    // The index of the last slash in dest, after the volume.
    let last_slash = |dest: &str, vol_len: usize| {
        dest.as_bytes()[vol_len..]
            .iter()
            .rposition(|&c| c == b'/')
            .map(|r| vol_len + r)
    };
    let mut links_walked = 0;
    let mut start = vol_len;
    while start < path.len() {
        let bytes = path.as_bytes();
        while start < bytes.len() && bytes[start] == b'/' {
            start += 1;
        }
        let mut end = start;
        while end < bytes.len() && bytes[end] != b'/' {
            end += 1;
        }

        // The next path component is in path[start:end].
        if end == start {
            // No more path components.
            break;
        }
        if &path[start..end] == "." {
            // Ignore path component ".".
            start = end;
            continue;
        }
        if &path[start..end] == ".." {
            // Back up to previous component if possible.
            // Note that volLen includes any leading slash.
            match last_slash(&dest, vol_len) {
                Some(r) if &dest[r + 1..] != ".." => {
                    // Discard everything since the last slash.
                    dest.truncate(r);
                }
                _ => {
                    // Either path has no slashes
                    // (it's empty or just "C:")
                    // or it ends in a ".." we had to keep.
                    // Either way, keep this "..".
                    if dest.len() > vol_len {
                        dest.push('/');
                    }
                    dest.push_str("..");
                }
            }
            start = end;
            continue;
        }

        // Ordinary path component. Add it to result.

        if !dest.is_empty() && !dest.ends_with('/') {
            dest.push('/');
        }

        dest.push_str(&path[start..end]);

        // Resolve symlink.

        let fi = std::fs::symlink_metadata(os_path(&dest))
            .map_err(|err| FsError::path("lstat", &dest, err))?;

        if !fi.file_type().is_symlink() {
            if !fi.is_dir() && end < path.len() {
                return Err(FsError::Other("not a directory".to_string()));
            }
            start = end;
            continue;
        }

        // Found symlink.

        links_walked += 1;
        if links_walked > 255 {
            return Err(FsError::Other("EvalSymlinks: too many links".to_string()));
        }

        let link = std::fs::read_link(os_path(&dest))
            .map(go_string_from_os)
            .map_err(|err| FsError::path("readlink", &dest, err))?;

        path = format!("{link}{}", &path[end..]);

        if link.starts_with('/') {
            // Symlink to absolute path.
            dest = "/".to_string();
            end = 1;
            vol = "/".to_string();
            vol_len = 1;
        } else {
            // Symlink to relative path; replace last
            // path component in dest.
            match last_slash(&dest, vol_len) {
                Some(r) => dest.truncate(r),
                None => dest = vol.clone(),
            }
            end = 0;
        }
        start = end;
    }
    Ok(filepath_clean(&dest))
}

// Go: realpath_windows.go:13 Realpath
// This implementation is based on what Node's fs.realpath.native does, via libuv: https://github.com/libuv/libuv/blob/ec5a4b54f7da7eeb01679005c615fee9633cdb3b/src/win/fs.c#L2937
// PORT: `std::fs::canonicalize` makes Go's calls: CreateFileW with no access,
// all share modes, OPEN_EXISTING and FILE_FLAG_BACKUP_SEMANTICS (Go
// `openMetadata`), then GetFinalPathNameByHandleW with VOLUME_NAME_DOS. It
// handles long paths itself (Go uses `os.Open` for them). The prefix
// handling below is Go's.
#[cfg(windows)]
pub fn realpath(path: &str) -> Result<String, FsError> {
    let s = std::fs::canonicalize(os_path(path))
        .map(go_string_from_os)
        .map_err(|err| FsError::path("CreateFile", path, err))?;
    if s.len() > 4 && s.starts_with(r"\\?\") {
        let s = &s[4..];
        if s.len() > 3 && s.starts_with("UNC") {
            // return path like \\server\share\...
            return Ok(format!(r"\{}", &s[3..]));
        }
        return Ok(s.to_string());
    }
    Err(FsError::Other(format!(
        "GetFinalPathNameByHandle returned unexpected path: {s}"
    )))
}

// Go: eintr_unix.go:7 ignoringEINTR
fn ignoring_eintr<T>(mut f: impl FnMut() -> io::Result<T>) -> io::Result<T> {
    loop {
        match f() {
            Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
            result => return result,
        }
    }
}

// Go: symlink_windows.go:8 IsSymlinkOrReparsePoint
/// Reports whether `path` has FILE_ATTRIBUTE_REPARSE_POINT (a symlink, a
/// junction or another reparse point).
///
/// PORT: Go GetFileAttributesEx (with `\\?\` for a long path) does not
/// follow the reparse point; `std::fs::symlink_metadata` does not either and
/// handles long paths itself.
#[cfg(windows)]
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    use std::os::windows::fs::MetadataExt;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x400;
    std::fs::symlink_metadata(os_path(path))
        .is_ok_and(|info| info.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0)
}

// Go: symlink_other.go:7 IsSymlinkOrReparsePoint
/// Reports whether `path` itself is a symlink. Go `os.Lstat` does not follow
/// the last link, and a path that cannot be read (missing, empty, holds a NUL
/// byte) is not a symlink.
#[cfg(not(windows))]
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    std::fs::symlink_metadata(os_path(path)).is_ok_and(|info| info.file_type().is_symlink())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;

    /// A new empty dir under the temp dir, as a real path (the macOS temp dir
    /// is under the link /var).
    fn temp_root(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!("ts_goport_{name}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        eval_symlinks(&go_string_from_os(dir)).unwrap()
    }

    /// The layout of issue #50 under `root`: the npm workspace `Work/Mono`
    /// with `node_modules/@acme/lib -> ../../packages/lib`, and the absolute
    /// link `abs -> <root>/Work/Mono/packages`.
    fn workspace(root: &str) -> String {
        let mono = format!("{root}/Work/Mono");
        for dir in ["packages/lib/src", "packages/app/src", "node_modules/@acme"] {
            std::fs::create_dir_all(format!("{mono}/{dir}")).unwrap();
        }
        std::fs::write(format!("{mono}/packages/lib/src/index.ts"), "").unwrap();
        symlink(
            "../../packages/lib",
            format!("{mono}/node_modules/@acme/lib"),
        )
        .unwrap();
        symlink(format!("{mono}/packages"), format!("{root}/abs")).unwrap();
        mono
    }

    // PORT: not in Go (path/filepath tests EvalSymlinks). On a case-sensitive
    // file system the Linux realpath (O_PATH and /proc/self/fd) gives the same
    // results.
    #[test]
    fn eval_symlinks_replaces_link_parts() {
        let root = temp_root("eval_symlinks");
        let mono = workspace(&root);
        let ok = |path: &str, want: &str| {
            assert_eq!(eval_symlinks(path).ok().as_deref(), Some(want), "{path}");
            assert_eq!(realpath(path).ok().as_deref(), Some(want), "{path}");
        };
        // A relative link goes on from the dir that holds it.
        ok(
            &format!("{mono}/node_modules/@acme/lib/src/index.ts"),
            &format!("{mono}/packages/lib/src/index.ts"),
        );
        // An absolute link starts again at the root.
        ok(
            &format!("{root}/abs/lib/src"),
            &format!("{mono}/packages/lib/src"),
        );
        // "." and extra slashes go. A ".." after a link goes to the parent of
        // the link target.
        ok(
            &format!("{mono}/./node_modules//@acme/lib/../app/"),
            &format!("{mono}/packages/app"),
        );
        let (_, name) = root.rsplit_once('/').unwrap();
        ok(&format!("{root}/../{name}"), &root);
        ok("/..", "/");

        // A missing part, a file with parts after it, a dangling link and a
        // link loop fail.
        symlink("missing", format!("{root}/dangling")).unwrap();
        symlink("loop2", format!("{root}/loop1")).unwrap();
        symlink("loop1", format!("{root}/loop2")).unwrap();
        for path in [
            format!("{mono}/missing/x"),
            format!("{mono}/packages/lib/src/index.ts/x"),
            format!("{root}/dangling"),
            format!("{root}/loop1/x"),
        ] {
            assert!(eval_symlinks(&path).is_err(), "{path}");
        }
        let _ = std::fs::remove_dir_all(&root);
    }

    // PORT: not in Go. Issue #50: on a case-insensitive file system (macOS
    // APFS and HFS+ by default) each part that is not a link keeps the
    // caller's spelling, and a link part gets the spelling of the link text,
    // whatever the stored names are. The test returns at once when the temp
    // dir is case-sensitive.
    #[test]
    fn eval_symlinks_keeps_the_callers_case() {
        let root = temp_root("eval_symlinks_case");
        let mono = workspace(&root);
        if std::fs::symlink_metadata(format!("{root}/wORK")).is_err() {
            let _ = std::fs::remove_dir_all(&root);
            return;
        }
        symlink(
            "../../packages/Lib",
            format!("{mono}/node_modules/@acme/rev"),
        )
        .unwrap();
        let ok = |path: &str, want: &str| {
            assert_eq!(eval_symlinks(path).ok().as_deref(), Some(want), "{path}");
            // PORT: the Linux realpath gives the name that the kernel's
            // dentry cache holds, as Go on Linux does.
            #[cfg(not(target_os = "linux"))]
            assert_eq!(realpath(path).ok().as_deref(), Some(want), "{path}");
        };
        let typed = format!("{root}/work/mono");
        ok(
            &format!("{typed}/node_modules/@acme/lib/src/index.ts"),
            &format!("{typed}/packages/lib/src/index.ts"),
        );
        ok(
            &format!("{root}/WORK/MONO/Packages/LIB"),
            &format!("{root}/WORK/MONO/Packages/LIB"),
        );
        // The link text "../../packages/Lib" names the stored "lib".
        ok(
            &format!("{mono}/node_modules/@acme/rev/src"),
            &format!("{mono}/packages/Lib/src"),
        );
        // The absolute link text is "<root>/Work/Mono/packages".
        ok(&format!("{root}/ABS/LIB"), &format!("{mono}/packages/LIB"));
        let _ = std::fs::remove_dir_all(&root);
    }

    // Go: realpath_darwin_test.go:11 TestRealpathHardlinkedFile
    // PORT: Go runs it on darwin only (the file name). The port runs it on
    // every unix, so the Linux test hosts run it too: on Linux the open of
    // `alias` gives the dentry of that name, and /proc/self/fd reads it back.
    // `t.TempDir()` is a new dir that is not resolved, as here.
    #[test]
    fn realpath_hardlinked_file() {
        use std::sync::atomic::{AtomicBool, Ordering};

        // Go `t.TempDir()` removes the dir when the test ends, also after a
        // failed check: the guard removes it on return and on panic.
        struct RemoveOnDrop(std::path::PathBuf);
        impl Drop for RemoveOnDrop {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let tmp = std::env::temp_dir().join(format!(
            "ts_goport_realpath_hardlink_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).unwrap();
        let _remove_tmp = RemoveOnDrop(tmp.clone());
        let real_path = tmp.join("real.d.ts");
        let alias = tmp.join("alias.d.ts");
        std::fs::write(&real_path, "export * from './lib';\n").unwrap();
        std::fs::hard_link(&real_path, &alias).unwrap();
        let alias = go_string_from_os(alias.into_os_string());

        let want = eval_symlinks(&alias).unwrap();

        // Go: the worker goroutine opens and closes the real name until
        // `stop` closes; its first error ends it. The guard is Go's
        // `defer stopWorker()`: a failed check stops the worker before the
        // scope joins it.
        struct StopOnDrop<'a>(&'a AtomicBool);
        impl Drop for StopOnDrop<'_> {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Relaxed);
            }
        }
        let stop = AtomicBool::new(false);
        let worker_err = std::thread::scope(|scope| {
            let worker = scope.spawn(|| {
                while !stop.load(Ordering::Relaxed) {
                    let opened = std::fs::File::open(&real_path);
                    // Go `openErr = f.Close()`.
                    // PORT: std has no File close that returns the error (a
                    // drop ignores it), and a raw close(2) needs `unsafe`.
                    // nix's safe `close` returns it, but nix is a
                    // dependency on Linux only, so other unix hosts check
                    // the open only.
                    #[cfg(target_os = "linux")]
                    let opened =
                        opened.and_then(|f| nix::unistd::close(f).map_err(std::io::Error::from));
                    if let Err(err) = opened {
                        return Some(err);
                    }
                }
                None
            });
            let stop_worker = StopOnDrop(&stop);
            for _ in 0..200 {
                assert_eq!(realpath(&alias).unwrap(), want);
            }
            drop(stop_worker);
            worker.join().unwrap()
        });
        assert!(worker_err.is_none(), "{worker_err:?}");
    }
}
