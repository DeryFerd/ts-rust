//! Go: internal/vfs/vfs.go and internal/vfs/internal/internal.go.
//!
//! The Go standard library types that `vfs.FS` uses (`io/fs.FileInfo`,
//! `io/fs.DirEntry`, `io/fs.FileMode`, the `io/fs` error values and the
//! `fs.Stat`, `fs.ReadDir`, `fs.ReadFile` and `fs.WalkDir` helpers) are
//! ported here too, because Rust has no equivalent with the same behavior.

use crate::frontend::prelude::*;
use std::io;
use std::time::SystemTime;

// Go: vfs.go:12 FS
// FS is a file system abstraction.
// PORT: Go interface values are shared pointers, so every method takes
// `&self`. Implementations that cache use interior mutability. Go
// `time.Time` parameters are `Option<SystemTime>`; `None` is the Go zero
// time.
pub trait Fs {
    // UseCaseSensitiveFileNames returns true if the file system is case-sensitive.
    fn use_case_sensitive_file_names(&self) -> bool;

    // FileExists returns true if the file exists.
    fn file_exists(&self, path: &str) -> bool;

    // ReadFile reads the file specified by path and returns the content.
    // If the file fails to be read, ok will be false.
    fn read_file(&self, path: &str) -> (String, bool);

    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError>;

    // AppendFile appends data to the file at path, creating it if it does not exist.
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError>;

    // Removes `path` and all its contents. Will return the first error it encounters.
    fn remove(&self, path: &str) -> Result<(), FsError>;

    // Chtimes changes the access and modification times of the named
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError>;

    // DirectoryExists returns true if the path is a directory.
    fn directory_exists(&self, path: &str) -> bool;

    // GetAccessibleEntries returns the files/directories in the specified directory.
    // If any entry is a symlink, it will be followed.
    fn get_accessible_entries(&self, path: &str) -> Entries;

    // PORT: Go returns a nil `fs.FileInfo` interface when the path cannot be
    // read; that is `None`.
    fn stat(&self, path: &str) -> Option<FileInfo>;

    // WalkDir walks the file tree rooted at root, calling walkFn for each file or directory in the tree.
    // It is has the same behavior as [fs.WalkDir], but with paths as [string].
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError>;

    // Realpath returns the "real path" of the specified path,
    // following symlinks and correcting filename casing.
    fn realpath(&self, path: &str) -> String;
}

// Go: vfs.go:52 Entries
#[derive(Clone, Debug, Default)]
pub struct Entries {
    pub files: Vec<String>,
    pub directories: Vec<String>,
    // Symlinks contains the names of entries in Files or Directories that were
    // originally symbolic links (or reparse points) on disk. The names are the
    // same as those in Files/Directories (i.e., the link name, not the target).
    // nil means symlink information is not available and the entries may need
    // to be re-checked for symlinks.
    // PORT: the Go nil map is `None`; an empty non-nil map is `Some(empty)`.
    pub symlinks: Option<FxHashSet<String>>,
}

// Go: io/fs/fs.go FileMode
// PORT: Go standard library type. Same bit values as Go.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct FileMode(pub u32);

impl FileMode {
    pub const DIR: FileMode = FileMode(1 << 31);
    pub const APPEND: FileMode = FileMode(1 << 30);
    pub const EXCLUSIVE: FileMode = FileMode(1 << 29);
    pub const TEMPORARY: FileMode = FileMode(1 << 28);
    pub const SYMLINK: FileMode = FileMode(1 << 27);
    pub const DEVICE: FileMode = FileMode(1 << 26);
    pub const NAMED_PIPE: FileMode = FileMode(1 << 25);
    pub const SOCKET: FileMode = FileMode(1 << 24);
    pub const SETUID: FileMode = FileMode(1 << 23);
    pub const SETGID: FileMode = FileMode(1 << 22);
    pub const CHAR_DEVICE: FileMode = FileMode(1 << 21);
    pub const STICKY: FileMode = FileMode(1 << 20);
    pub const IRREGULAR: FileMode = FileMode(1 << 19);
    pub const TYPE: FileMode = FileMode(
        Self::DIR.0
            | Self::SYMLINK.0
            | Self::NAMED_PIPE.0
            | Self::SOCKET.0
            | Self::DEVICE.0
            | Self::CHAR_DEVICE.0
            | Self::IRREGULAR.0,
    );
    pub const PERM: FileMode = FileMode(0o777);

    // Go: io/fs/fs.go FileMode.IsDir
    pub fn is_dir(self) -> bool {
        self.0 & Self::DIR.0 != 0
    }

    // Go: io/fs/fs.go FileMode.IsRegular
    pub fn is_regular(self) -> bool {
        self.0 & Self::TYPE.0 == 0
    }

    // Go: io/fs/fs.go FileMode.Perm
    pub fn perm(self) -> FileMode {
        FileMode(self.0 & Self::PERM.0)
    }

    // Go: io/fs/fs.go FileMode.Type
    pub fn type_(self) -> FileMode {
        FileMode(self.0 & Self::TYPE.0)
    }

    pub fn intersects(self, other: FileMode) -> bool {
        self.0 & other.0 != 0
    }
}

impl std::ops::BitOr for FileMode {
    type Output = FileMode;
    fn bitor(self, rhs: FileMode) -> FileMode {
        FileMode(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for FileMode {
    fn bitor_assign(&mut self, rhs: FileMode) {
        self.0 |= rhs.0;
    }
}

// Go: vfs.go:68 FileInfo (= io/fs.FileInfo)
// PORT: the Go interface becomes a plain value. `Sys()` is not ported
// (nothing in scope reads it). `mod_time: None` is the Go zero time.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FileInfo {
    pub name: String,
    pub size: i64,
    pub mode: FileMode,
    pub mod_time: Option<SystemTime>,
}

impl FileInfo {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn size(&self) -> i64 {
        self.size
    }

    pub fn mode(&self) -> FileMode {
        self.mode
    }

    pub fn mod_time(&self) -> Option<SystemTime> {
        self.mod_time
    }

    pub fn is_dir(&self) -> bool {
        self.mode.is_dir()
    }
}

// PORT: where `DirEntry.Info()` gets its data. Entries from `os.ReadDir`
// call `lstat` on the full path; entries made from a `FileInfo`
// (`fs.FileInfoToDirEntry`, the bundled file system) return that value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DirEntryInfo {
    Known(FileInfo),
    Lstat(String),
}

// Go: vfs.go:65 DirEntry (= io/fs.DirEntry)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirEntry {
    pub name: String,
    pub typ: FileMode,
    pub info: DirEntryInfo,
}

impl DirEntry {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn is_dir(&self) -> bool {
        self.typ.is_dir()
    }

    pub fn type_(&self) -> FileMode {
        self.typ
    }

    pub fn info(&self) -> Result<FileInfo, FsError> {
        match &self.info {
            DirEntryInfo::Known(info) => Ok(info.clone()),
            DirEntryInfo::Lstat(full_path) => match std::fs::symlink_metadata(os_path(full_path)) {
                Ok(md) => Ok(file_info_from_metadata(basename(full_path), &md)),
                Err(err) => Err(FsError::path("lstat", full_path, err)),
            },
        }
    }
}

// Go: io/fs/readdir.go FileInfoToDirEntry
// PORT: Go returns nil for a nil info; callers here always have a value.
pub fn file_info_to_dir_entry(info: FileInfo) -> DirEntry {
    DirEntry {
        name: info.name.clone(),
        typ: info.mode.type_(),
        info: DirEntryInfo::Known(info),
    }
}

// Go: vfs.go:71 ErrInvalid, ErrPermission, ErrExist, ErrNotExist, ErrClosed,
// vfs.go:82 SkipAll, SkipDir
// PORT: Go `error` values become one enum. `Path` is `*os.PathError`
// (the OS error is shared so the value can be cloned). `Other` is an
// `errors.New` message.
#[derive(Clone, Debug)]
pub enum FsError {
    Invalid,
    Permission,
    Exist,
    NotExist,
    Closed,
    SkipAll,
    SkipDir,
    Path {
        op: &'static str,
        path: String,
        err: Rc<io::Error>,
    },
    Other(String),
}

impl FsError {
    // PORT: builds a Go `*os.PathError`.
    pub fn path(op: &'static str, path: &str, err: io::Error) -> FsError {
        FsError::Path {
            op,
            path: path.to_string(),
            err: Rc::new(err),
        }
    }

    pub fn is_skip_all(&self) -> bool {
        matches!(self, FsError::SkipAll)
    }

    pub fn is_skip_dir(&self) -> bool {
        matches!(self, FsError::SkipDir)
    }
}

// Go: vfs.go:80 WalkDirFunc (= io/fs.WalkDirFunc)
// PORT: Go passes a nil `DirEntry` and a nil `error` as `None`.
pub type WalkDirFunc<'a> =
    dyn FnMut(&str, Option<&DirEntry>, Option<FsError>) -> Result<(), FsError> + 'a;

// PORT: the Go `io/fs.FS` value that `Common.RootFor` returns, with the
// `StatFS`, `ReadDirFS` and `ReadFileFS` methods that `fs.Stat`,
// `fs.ReadDir` and `fs.ReadFile` use. `os.DirFS` (osvfs.rs `DirFs`) is the
// only implementation in scope.
pub trait IoFs {
    fn stat(&self, name: &str) -> Result<FileInfo, FsError>;
    // Go os.ReadDir returns the entries sorted by file name.
    fn read_dir(&self, name: &str) -> Result<Vec<DirEntry>, FsError>;
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError>;
}

// Go: internal.go:15 Common
// PORT: Go func fields become fn pointers. A nil `IsReparsePoint` is `None`.
pub struct Common {
    pub root_for: fn(&str) -> Option<Box<dyn IoFs>>,
    pub is_reparse_point: Option<fn(&str) -> bool>,
}

// Go: internal.go:20 RootLength
pub fn root_length(p: &str) -> i32 {
    let l = get_encoded_root_length(p);
    if l == 0 {
        panic!("vfs: path {p:?} is not absolute");
    } else if l < 0 {
        return !l;
    }
    l
}

// Go: internal.go:30 SplitPath
pub fn split_path(p: &str) -> (String, String) {
    let p: String = normalize_path(p).into();
    let l = root_length(&p) as usize;
    let root_name = p[..l].to_string();
    let rest: String = remove_trailing_directory_separator(&p[l..]).into();
    (root_name, rest)
}

impl Common {
    // Go: internal.go:38 RootAndPath
    pub fn root_and_path(&self, path: &str) -> (Option<Box<dyn IoFs>>, String, String) {
        let (root_name, mut rest) = split_path(path);
        if rest.is_empty() {
            rest = ".".to_string();
        }
        ((self.root_for)(&root_name), root_name, rest)
    }

    // Go: internal.go:46 Stat
    pub fn stat(&self, path: &str) -> Option<FileInfo> {
        let (fsys, _, rest) = self.root_and_path(path);
        let fsys = fsys?;
        // PORT: Go `fs.Stat` calls the `StatFS` method directly.
        fsys.stat(&rest).ok()
    }

    // Go: internal.go:58 FileExists
    pub fn file_exists(&self, path: &str) -> bool {
        let stat = self.stat(path);
        matches!(stat, Some(stat) if !stat.is_dir())
    }

    // Go: internal.go:63 DirectoryExists
    pub fn directory_exists(&self, path: &str) -> bool {
        let stat = self.stat(path);
        matches!(stat, Some(stat) if stat.is_dir())
    }

    // Go: internal.go:68 GetAccessibleEntries
    pub fn get_accessible_entries(&self, path: &str) -> Entries {
        let mut result = Entries {
            symlinks: Some(FxHashSet::default()),
            ..Entries::default()
        };

        // PORT: the Go closure `addToResult` takes the result explicitly.
        fn add_to_result(result: &mut Entries, name: &str, mode: FileMode, is_link: bool) -> bool {
            if mode.is_dir() {
                result.directories.push(name.to_string());
            } else if mode.is_regular() {
                result.files.push(name.to_string());
            } else {
                return false;
            }

            if is_link {
                if let Some(symlinks) = result.symlinks.as_mut() {
                    symlinks.insert(name.to_string());
                }
            }
            true
        }

        for entry in self.get_entries(path) {
            let entry_type = entry.type_();

            if add_to_result(&mut result, entry.name(), entry_type, false) {
                continue;
            }

            if entry_type.intersects(FileMode::SYMLINK) {
                // Easy case; UNIX-like system will clearly mark symlinks.
                if let Some(stat) = self.stat(&format!("{}/{}", path, entry.name())) {
                    add_to_result(&mut result, entry.name(), stat.mode(), true);
                }
                continue;
            }

            if entry_type.intersects(FileMode::IRREGULAR) {
                if let Some(is_reparse_point) = self.is_reparse_point {
                    // Could be a Windows junction or other reparse point.
                    // Check using the OS-specific helper.
                    let full_path = format!("{}/{}", path, entry.name());
                    if is_reparse_point(&full_path) {
                        if let Some(stat) = self.stat(&full_path) {
                            add_to_result(&mut result, entry.name(), stat.mode(), true);
                        }
                    }
                    continue;
                }
            }
        }

        result
    }

    // Go: internal.go:117 getEntries
    fn get_entries(&self, path: &str) -> Vec<DirEntry> {
        let (fsys, _, rest) = self.root_and_path(path);
        let Some(fsys) = fsys else {
            return Vec::new();
        };

        // PORT: Go `fs.ReadDir` calls the `ReadDirFS` method directly.
        match fsys.read_dir(&rest) {
            Ok(entries) => entries,
            Err(_) => Vec::new(),
        }
    }

    // Go: internal.go:131 WalkDir
    pub fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        let (fsys, root_name, rest) = self.root_and_path(root);
        let Some(fsys) = fsys else {
            return Ok(());
        };
        io_fs_walk_dir(
            fsys.as_ref(),
            &rest,
            &mut |path: &str, d: Option<&DirEntry>, err: Option<FsError>| {
                let path = if path == "." { "" } else { path };
                walk_fn(&format!("{root_name}{path}"), d, err)
            },
        )
    }

    // Go: internal.go:144 ReadFile
    pub fn read_file(&self, path: &str) -> (String, bool) {
        let (fsys, _, rest) = self.root_and_path(path);
        let Some(fsys) = fsys else {
            return (String::new(), false);
        };

        // PORT: Go `fs.ReadFile` calls the `ReadFileFS` method directly.
        let b = match fsys.read_file(&rest) {
            Ok(b) => b,
            Err(_) => return (String::new(), false),
        };

        // An invariant of any underlying filesystem is that the bytes returned
        // are immutable, otherwise anyone using the filesystem would end up
        // with data races.
        //
        // This means that we can safely convert the bytes to a string directly,
        // saving a copy.
        if b.is_empty() {
            return (String::new(), true);
        }

        decode_bytes(b)
    }
}

// Go: internal.go:170 decodeBytes
// PORT: takes the bytes instead of a Go string that holds them. Go returns
// the bytes unchanged, so a Go string can hold invalid UTF-8. A Rust String
// cannot, so the text is the port form of the Go string
// (`scanner_util::go_string_from_bytes`, see `scanner_util::GO_STRING_MARKER`).
fn decode_bytes(mut s: Vec<u8>) -> (String, bool) {
    if s.len() >= 2 {
        match [s[0], s[1]] {
            [0xFF, 0xFE] => {
                return (
                    crate::scanner_util::go_string_from_utf8(decode_utf16(&s[2..], false)),
                    true,
                );
            }
            [0xFE, 0xFF] => {
                return (
                    crate::scanner_util::go_string_from_utf8(decode_utf16(&s[2..], true)),
                    true,
                );
            }
            _ => {}
        }
    }
    if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF {
        s.drain(..3);
    }

    (crate::scanner_util::go_string_from_bytes(s), true)
}

// Go: internal.go:188 decodeUtf16
// PORT: `order binary.ByteOrder` is `big_endian`. Go `binary.Read` reads
// len(s)/2 values and ignores an odd last byte; it cannot fail here.
// `utf16.Decode` replaces unpaired surrogates with U+FFFD, like
// `String::from_utf16_lossy`.
fn decode_utf16(s: &[u8], big_endian: bool) -> String {
    let ints: Vec<u16> = s
        .chunks_exact(2)
        .map(|pair| {
            if big_endian {
                u16::from_be_bytes([pair[0], pair[1]])
            } else {
                u16::from_le_bytes([pair[0], pair[1]])
            }
        })
        .collect();
    String::from_utf16_lossy(&ints)
}

// Go: io/fs/walk.go WalkDir
// PORT: Go standard library. `fs.Stat` calls the `StatFS` method directly.
pub fn io_fs_walk_dir(
    fsys: &dyn IoFs,
    root: &str,
    walk_fn: &mut WalkDirFunc<'_>,
) -> Result<(), FsError> {
    let result = match fsys.stat(root) {
        Err(err) => walk_fn(root, None, Some(err)),
        Ok(info) => io_fs_walk_dir_inner(fsys, root, &file_info_to_dir_entry(info), walk_fn),
    };
    match result {
        Err(FsError::SkipDir) | Err(FsError::SkipAll) => Ok(()),
        other => other,
    }
}

// Go: io/fs/walk.go walkDir
fn io_fs_walk_dir_inner(
    fsys: &dyn IoFs,
    name: &str,
    d: &DirEntry,
    walk_dir_fn: &mut WalkDirFunc<'_>,
) -> Result<(), FsError> {
    let first = walk_dir_fn(name, Some(d), None);
    if first.is_err() || !d.is_dir() {
        if matches!(first, Err(FsError::SkipDir)) && d.is_dir() {
            return Ok(());
        }
        return first;
    }

    let dirs = match fsys.read_dir(name) {
        Ok(dirs) => dirs,
        Err(err) => {
            // Second call, to report ReadDir error.
            let second = walk_dir_fn(name, Some(d), Some(err));
            if let Err(err) = second {
                if err.is_skip_dir() && d.is_dir() {
                    return Ok(());
                }
                return Err(err);
            }
            // PORT: Go keeps the entries that `ReadDir` returned before the
            // error. The `ReadDirFS` port returns none on error.
            Vec::new()
        }
    };

    for d1 in &dirs {
        // PORT: Go `path.Join(name, d1.Name())`. `name` is already clean and
        // an entry name has no '/', so Join only drops a leading ".".
        let name1 = if name == "." {
            d1.name().to_string()
        } else {
            format!("{}/{}", name, d1.name())
        };
        if let Err(err) = io_fs_walk_dir_inner(fsys, &name1, d1, walk_dir_fn) {
            if err.is_skip_dir() {
                break;
            }
            return Err(err);
        }
    }
    Ok(())
}

// Go: io/fs/fs.go ValidPath
// PORT: Go standard library, used by the `os.DirFS` port. `name` is a port
// form (see `scanner_util::GO_STRING_MARKER`); its Go bytes are valid UTF-8
// when it has no invalid byte or lone surrogate unit.
pub fn io_fs_valid_path(name: &str) -> bool {
    if crate::scanner_util::contains_go_string_marker(name)
        && std::str::from_utf8(&crate::scanner_util::go_string_bytes(name)).is_err()
    {
        return false;
    }

    if name == "." {
        // special case
        return true;
    }

    // Iterate over elements in name, checking each.
    let mut name = name;
    loop {
        let (elem, rest, more) = match name.find('/') {
            Some(i) => (&name[..i], &name[i + 1..], true),
            None => (name, "", false),
        };
        if elem.is_empty() || elem == "." || elem == ".." {
            return false;
        }
        if !more {
            return true;
        }
        name = rest;
    }
}

// Go: os/stat_linux.go fillFileStatFromSys
// PORT: Go standard library. Converts Rust metadata to the Go `FileInfo`
// with the same mode bits.
pub fn file_info_from_metadata(name: &str, md: &std::fs::Metadata) -> FileInfo {
    use std::os::unix::fs::MetadataExt;
    const S_IFMT: u32 = 0o170000;
    const S_IFBLK: u32 = 0o060000;
    const S_IFCHR: u32 = 0o020000;
    const S_IFDIR: u32 = 0o040000;
    const S_IFIFO: u32 = 0o010000;
    const S_IFLNK: u32 = 0o120000;
    const S_IFREG: u32 = 0o100000;
    const S_IFSOCK: u32 = 0o140000;
    const S_ISGID: u32 = 0o2000;
    const S_ISUID: u32 = 0o4000;
    const S_ISVTX: u32 = 0o1000;

    let sys_mode = md.mode();
    let mut mode = FileMode(sys_mode & 0o777);
    match sys_mode & S_IFMT {
        S_IFBLK => mode |= FileMode::DEVICE,
        S_IFCHR => mode |= FileMode::DEVICE | FileMode::CHAR_DEVICE,
        S_IFDIR => mode |= FileMode::DIR,
        S_IFIFO => mode |= FileMode::NAMED_PIPE,
        S_IFLNK => mode |= FileMode::SYMLINK,
        S_IFREG => {
            // nothing to do
        }
        S_IFSOCK => mode |= FileMode::SOCKET,
        _ => {}
    }
    if sys_mode & S_ISGID != 0 {
        mode |= FileMode::SETGID;
    }
    if sys_mode & S_ISUID != 0 {
        mode |= FileMode::SETUID;
    }
    if sys_mode & S_ISVTX != 0 {
        mode |= FileMode::STICKY;
    }
    FileInfo {
        name: name.to_string(),
        size: md.size() as i64,
        mode,
        mod_time: md.modified().ok(),
    }
}

// Go: os/path_unix.go basename
// PORT: Go standard library. Removes trailing slashes and the leading
// directory name.
pub fn basename(name: &str) -> &str {
    let mut name = name;
    // Remove trailing slashes
    while name.len() > 1 && name.ends_with('/') {
        name = &name[..name.len() - 1];
    }
    // Remove leading directory name
    // PORT: Go starts the search one byte before the last byte.
    if name.len() > 1 {
        if let Some(i) = name.as_bytes()[..name.len() - 1]
            .iter()
            .rposition(|&b| b == b'/')
        {
            name = &name[i + 1..];
        }
    }
    name
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scanner_util::{GoUnit, go_string_bytes, go_unit_at};

    /// The units of a port form string.
    fn units(text: &str) -> Vec<GoUnit> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < text.len() {
            let (unit, size) = go_unit_at(text, i);
            out.push(unit);
            i += size;
        }
        out
    }

    // Each invalid byte is one unit, as Go reads one RuneError per byte. Real
    // U+EF80..U+EFFF, U+FDD0 and U+10F7xx chars stay chars. A file write
    // gives the source bytes back.
    #[test]
    fn invalid_utf8_bytes_round_trip() {
        let source: Vec<u8> = [
            &b"/\x80/u \xE2\x82A \xF0\x90\x80 \xFF\xE2\x82\xAC \xED\xA0\x80 "[..],
            "\u{EF80}\u{EFFF}\u{FDD0}\u{FDD0}\u{10F7FF}\u{10FFFF}\u{FDD0}".as_bytes(),
        ]
        .concat();
        let (text, ok) = decode_bytes(source.clone());
        assert!(ok);
        let units = units(&text);
        let invalid: Vec<u8> = units
            .iter()
            .filter_map(|unit| match unit {
                GoUnit::InvalidByte(b) => Some(*b),
                _ => None,
            })
            .collect();
        assert_eq!(
            invalid,
            [0x80, 0xE2, 0x82, 0xF0, 0x90, 0x80, 0xFF, 0xED, 0xA0, 0x80]
        );
        assert!(units.contains(&GoUnit::Char('\u{20AC}')));
        assert!(units.contains(&GoUnit::Char('\u{EF80}')));
        assert!(units.contains(&GoUnit::Char('\u{10F7FF}')));
        assert_eq!(
            units
                .iter()
                .filter(|&&unit| unit == GoUnit::Char('\u{FDD0}'))
                .count(),
            3
        );
        assert_eq!(&*go_string_bytes(&text), &source[..]);
        assert!(matches!(
            go_string_bytes("a\u{EF80}\u{EE00}b"),
            std::borrow::Cow::Borrowed(_)
        ));
    }
}
