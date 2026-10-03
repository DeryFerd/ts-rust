//! Go: internal/vfs/wrapvfs/wrapvfs.go

use crate::frontend::prelude::*;
use std::time::SystemTime;

// Go: wrapvfs.go:9 Replacements
// PORT: nil Go funcs are `None`. `time.Time` is `Option<SystemTime>`
// (`None` is the Go zero time), as in the `Fs` trait.
#[derive(Default)]
pub struct Replacements {
    pub use_case_sensitive_file_names: Option<Box<dyn Fn() -> bool>>,
    pub file_exists: Option<Box<dyn Fn(&str) -> bool>>,
    pub read_file: Option<Box<dyn Fn(&str) -> (String, bool)>>,
    pub write_file: Option<Box<dyn Fn(&str, &str) -> Result<(), FsError>>>,
    pub append_file: Option<Box<dyn Fn(&str, &str) -> Result<(), FsError>>>,
    pub remove: Option<Box<dyn Fn(&str) -> Result<(), FsError>>>,
    pub chtimes:
        Option<Box<dyn Fn(&str, Option<SystemTime>, Option<SystemTime>) -> Result<(), FsError>>>,
    pub directory_exists: Option<Box<dyn Fn(&str) -> bool>>,
    pub get_accessible_entries: Option<Box<dyn Fn(&str) -> Entries>>,
    pub stat: Option<Box<dyn Fn(&str) -> Option<FileInfo>>>,
    pub realpath: Option<Box<dyn Fn(&str) -> String>>,
}

// Go: wrapvfs.go:23 Wrap
// PORT: the Go package function `wrapvfs.Wrap` is `wrapvfs_wrap`.
pub fn wrapvfs_wrap(fs: Rc<dyn Fs>, replacements: Replacements) -> Rc<dyn Fs> {
    Rc::new(WrappedFs { fs, replacements })
}

// Go: wrapvfs.go:30 wrappedFS
struct WrappedFs {
    fs: Rc<dyn Fs>,
    replacements: Replacements,
}

impl Fs for WrappedFs {
    // Go: wrapvfs.go:36 UseCaseSensitiveFileNames
    // UseCaseSensitiveFileNames implements [vfs.FS].
    fn use_case_sensitive_file_names(&self) -> bool {
        if let Some(f) = &self.replacements.use_case_sensitive_file_names {
            return f();
        }
        self.fs.use_case_sensitive_file_names()
    }

    // Go: wrapvfs.go:44 FileExists
    // FileExists implements [vfs.FS].
    fn file_exists(&self, path: &str) -> bool {
        if let Some(f) = &self.replacements.file_exists {
            return f(path);
        }
        self.fs.file_exists(path)
    }

    // Go: wrapvfs.go:52 ReadFile
    // ReadFile implements [vfs.FS].
    fn read_file(&self, path: &str) -> (String, bool) {
        if let Some(f) = &self.replacements.read_file {
            return f(path);
        }
        self.fs.read_file(path)
    }

    // Go: wrapvfs.go:60 WriteFile
    // WriteFile implements [vfs.FS].
    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        if let Some(f) = &self.replacements.write_file {
            return f(path, data);
        }
        self.fs.write_file(path, data)
    }

    // Go: wrapvfs.go:68 AppendFile
    // AppendFile implements [vfs.FS].
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        if let Some(f) = &self.replacements.append_file {
            return f(path, data);
        }
        self.fs.append_file(path, data)
    }

    // Go: wrapvfs.go:76 Remove
    // Remove implements [vfs.FS].
    fn remove(&self, path: &str) -> Result<(), FsError> {
        if let Some(f) = &self.replacements.remove {
            return f(path);
        }
        self.fs.remove(path)
    }

    // Go: wrapvfs.go:84 Chtimes
    // Chtimes implements [vfs.FS].
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        if let Some(f) = &self.replacements.chtimes {
            return f(path, a_time, m_time);
        }
        self.fs.chtimes(path, a_time, m_time)
    }

    // Go: wrapvfs.go:92 DirectoryExists
    // DirectoryExists implements [vfs.FS].
    fn directory_exists(&self, path: &str) -> bool {
        if let Some(f) = &self.replacements.directory_exists {
            return f(path);
        }
        self.fs.directory_exists(path)
    }

    // Go: wrapvfs.go:100 GetAccessibleEntries
    // GetAccessibleEntries implements [vfs.FS].
    fn get_accessible_entries(&self, path: &str) -> Entries {
        if let Some(f) = &self.replacements.get_accessible_entries {
            return f(path);
        }
        self.fs.get_accessible_entries(path)
    }

    // Go: wrapvfs.go:108 Stat
    // Stat implements [vfs.FS].
    fn stat(&self, path: &str) -> Option<FileInfo> {
        if let Some(f) = &self.replacements.stat {
            return f(path);
        }
        self.fs.stat(path)
    }

    // Go: wrapvfs.go:116 Realpath
    // Realpath implements [vfs.FS].
    fn realpath(&self, path: &str) -> String {
        if let Some(f) = &self.replacements.realpath {
            return f(path);
        }
        self.fs.realpath(path)
    }
}
