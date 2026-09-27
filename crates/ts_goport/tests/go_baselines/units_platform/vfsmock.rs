//! Go: `internal/vfs/vfsmock` (`wrapper.go`, the generated `FSMock`) and
//! its `wrapper_test.go`.
//!
//! PORT: Go `FSMock` has one func field per `vfs.FS` method and records
//! every call. `FsMock` implements the Rust `Fs` trait: each method records
//! its arguments and forwards to the wrapped FS, which is what Go `Wrap`
//! sets every func field to. `TestWrap` checks that every method forwards
//! (Go checks that no func field is nil).

use std::cell::RefCell;
use std::rc::Rc;
use std::time::SystemTime;

use ts_goport::frontend::vfs::{Entries, FileInfo, Fs, FsError, WalkDirFunc};

/// Go `FSMock.WriteFileCalls()` element.
#[derive(Clone, Debug)]
pub(crate) struct WriteFileCall {
    pub(crate) path: String,
    pub(crate) data: String,
}

/// The recorded calls of each method (Go `lock*` and `calls` fields).
#[derive(Default)]
pub(crate) struct Calls {
    pub(crate) use_case_sensitive_file_names: usize,
    pub(crate) file_exists: Vec<String>,
    pub(crate) read_file: Vec<String>,
    pub(crate) write_file: Vec<WriteFileCall>,
    pub(crate) append_file: Vec<WriteFileCall>,
    pub(crate) remove: Vec<String>,
    pub(crate) chtimes: Vec<String>,
    pub(crate) directory_exists: Vec<String>,
    pub(crate) get_accessible_entries: Vec<String>,
    pub(crate) stat: Vec<String>,
    pub(crate) walk_dir: Vec<String>,
    pub(crate) realpath: Vec<String>,
}

// Go: vfsmock/mock_generated.go FSMock
pub(crate) struct FsMock {
    inner: Rc<dyn Fs>,
    pub(crate) calls: RefCell<Calls>,
}

// Go: vfsmock/wrapper.go Wrap
pub(crate) fn wrap(fs: Rc<dyn Fs>) -> Rc<FsMock> {
    Rc::new(FsMock {
        inner: fs,
        calls: RefCell::new(Calls::default()),
    })
}

impl Fs for FsMock {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.calls.borrow_mut().use_case_sensitive_file_names += 1;
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.calls.borrow_mut().file_exists.push(path.to_string());
        self.inner.file_exists(path)
    }

    fn read_file(&self, path: &str) -> (String, bool) {
        self.calls.borrow_mut().read_file.push(path.to_string());
        self.inner.read_file(path)
    }

    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.calls.borrow_mut().write_file.push(WriteFileCall {
            path: path.to_string(),
            data: data.to_string(),
        });
        self.inner.write_file(path, data)
    }

    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.calls.borrow_mut().append_file.push(WriteFileCall {
            path: path.to_string(),
            data: data.to_string(),
        });
        self.inner.append_file(path, data)
    }

    fn remove(&self, path: &str) -> Result<(), FsError> {
        self.calls.borrow_mut().remove.push(path.to_string());
        self.inner.remove(path)
    }

    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        self.calls.borrow_mut().chtimes.push(path.to_string());
        self.inner.chtimes(path, a_time, m_time)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.calls
            .borrow_mut()
            .directory_exists
            .push(path.to_string());
        self.inner.directory_exists(path)
    }

    fn get_accessible_entries(&self, path: &str) -> Entries {
        self.calls
            .borrow_mut()
            .get_accessible_entries
            .push(path.to_string());
        self.inner.get_accessible_entries(path)
    }

    fn stat(&self, path: &str) -> Option<FileInfo> {
        self.calls.borrow_mut().stat.push(path.to_string());
        self.inner.stat(path)
    }

    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        self.calls.borrow_mut().walk_dir.push(root.to_string());
        self.inner.walk_dir(root, walk_fn)
    }

    fn realpath(&self, path: &str) -> String {
        self.calls.borrow_mut().realpath.push(path.to_string());
        self.inner.realpath(path)
    }
}

// Go: vfsmock/wrapper_test.go:11 TestWrap
#[test]
fn test_wrap() {
    let inner = crate::support::vfstest::from_map([("/a/b.txt", "hello")], true);
    let wrapper = wrap(Rc::clone(&inner));

    assert_eq!(
        wrapper.use_case_sensitive_file_names(),
        inner.use_case_sensitive_file_names()
    );
    assert_eq!(
        wrapper.file_exists("/a/b.txt"),
        inner.file_exists("/a/b.txt")
    );
    assert_eq!(wrapper.read_file("/a/b.txt"), inner.read_file("/a/b.txt"));
    assert_eq!(wrapper.directory_exists("/a"), inner.directory_exists("/a"));
    assert_eq!(
        wrapper.get_accessible_entries("/a").files,
        inner.get_accessible_entries("/a").files
    );
    assert_eq!(
        wrapper.stat("/a/b.txt").map(|i| i.size()),
        inner.stat("/a/b.txt").map(|i| i.size())
    );
    assert_eq!(wrapper.realpath("/a/b.txt"), inner.realpath("/a/b.txt"));
    let mut seen = Vec::new();
    wrapper
        .walk_dir("/a", &mut |path, _, _| {
            seen.push(path.to_string());
            Ok(())
        })
        .unwrap();
    assert_eq!(seen, vec!["/a", "/a/b.txt"]);
    wrapper.write_file("/a/c.txt", "x").unwrap();
    wrapper.append_file("/a/c.txt", "y").unwrap();
    assert_eq!(inner.read_file("/a/c.txt"), ("xy".to_string(), true));
    wrapper.chtimes("/a/c.txt", None, None).unwrap();
    wrapper.remove("/a/c.txt").unwrap();
    assert!(!inner.file_exists("/a/c.txt"));

    let calls = wrapper.calls.borrow();
    assert_eq!(calls.use_case_sensitive_file_names, 1);
    for (name, n) in [
        ("FileExists", calls.file_exists.len()),
        ("ReadFile", calls.read_file.len()),
        ("WriteFile", calls.write_file.len()),
        ("AppendFile", calls.append_file.len()),
        ("Remove", calls.remove.len()),
        ("Chtimes", calls.chtimes.len()),
        ("DirectoryExists", calls.directory_exists.len()),
        ("GetAccessibleEntries", calls.get_accessible_entries.len()),
        ("Stat", calls.stat.len()),
        ("WalkDir", calls.walk_dir.len()),
        ("Realpath", calls.realpath.len()),
    ] {
        assert_eq!(n, 1, "field {name}Func should not be zero; update Wrap");
    }
}
