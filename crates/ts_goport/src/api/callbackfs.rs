//! Port of internal/api/callbackfs.go.

use crate::api::prelude::*;

use crate::frontend::json::{
    JsonDecoder, JsonError, MarshalerTo, UnmarshalerFrom, json_unmarshal, json_unmarshal_decode,
};
use crate::frontend::json_ext::{
    AnyValue, marshal_field, unmarshal_struct_fields, write_object_end, write_object_start,
};
use crate::frontend::vfs::{Entries, FileInfo, Fs, FsError, WalkDirFunc};
use crate::gostd::{Context, GoError, errors};
use crate::ipc::Conn;
use std::time::SystemTime;

// Go: callbackfs.go:19 callbackFS
// callbackFS wraps a base filesystem and delegates certain operations
// to the client via RPC callbacks. This allows the API client to provide
// a virtual filesystem (e.g., in-memory files for testing).
//
// The callbacks to enable are specified at construction time via the
// --callbacks CLI flag. The connection is set via SetConnection after
// the transport connection is established.
pub struct CallbackFS {
    base: Rc<dyn Fs>,
    enabled_callbacks: FxHashMap<String, bool>,

    // conn and ctx are set after connection is established
    // PORT: `RefCell` so SetConnection works through the shared `Rc`; nil
    // is `None`.
    conn: RefCell<Option<Rc<dyn Conn>>>,
    ctx: RefCell<Option<Context>>,
}

// Go: callbackfs.go:29
// Callback names that can be enabled
const CALLBACK_READ_FILE: &str = "readFile";
const CALLBACK_FILE_EXISTS: &str = "fileExists";
const CALLBACK_DIRECTORY_EXISTS: &str = "directoryExists";
const CALLBACK_GET_ACCESSIBLE_ENTRIES: &str = "getAccessibleEntries";
const CALLBACK_REALPATH: &str = "realpath";
// tsgo#4699
const CALLBACK_WRITE_FILE: &str = "writeFile";

// Go: callbackfs.go:37 isCallbackName
fn is_callback_name(name: &str) -> bool {
    matches!(
        name,
        CALLBACK_READ_FILE
            | CALLBACK_FILE_EXISTS
            | CALLBACK_DIRECTORY_EXISTS
            | CALLBACK_GET_ACCESSIBLE_ENTRIES
            | CALLBACK_REALPATH
            | CALLBACK_WRITE_FILE
    )
}

// Go: callbackfs.go:53 newCallbackFS
// newCallbackFS creates a new callbackFS wrapping the given base filesystem.
// The callbacks slice specifies which filesystem operations should be delegated
// to the client (e.g., "readFile", "fileExists").
pub fn new_callback_fs(base: Rc<dyn Fs>, callbacks: &[String]) -> Rc<CallbackFS> {
    let mut enabled: FxHashMap<String, bool> =
        FxHashMap::with_capacity_and_hasher(callbacks.len(), Default::default());
    for cb in callbacks {
        if !is_callback_name(cb) {
            panic!("unknown callback name: {cb}");
        }
        enabled.insert(cb.clone(), true);
    }
    Rc::new(CallbackFS {
        base,
        enabled_callbacks: enabled,
        conn: RefCell::new(None),
        ctx: RefCell::new(None),
    })
}

// Go: the anonymous `struct { Content *string }` in ReadFile.
#[derive(Default)]
struct ReadFileWrapper {
    content: Option<String>,
}

impl UnmarshalerFrom for ReadFileWrapper {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "struct { Content *string }", |name, dec| {
            match name {
                "content" => json_unmarshal_decode(dec, &mut self.content)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = ReadFileWrapper::default();
        }
        Ok(())
    }
}

// Go: the anonymous `struct { Files []string; Directories []string }` in
// GetAccessibleEntries.
#[derive(Default)]
struct RawEntries {
    files: Vec<String>,
    directories: Vec<String>,
}

impl UnmarshalerFrom for RawEntries {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(
            dec,
            "struct { Files []string; Directories []string }",
            |name, dec| {
                match name {
                    "files" => json_unmarshal_decode(dec, &mut self.files)?,
                    "directories" => json_unmarshal_decode(dec, &mut self.directories)?,
                    _ => return Ok(false),
                }
                Ok(true)
            },
        )?;
        if !is_object {
            *self = RawEntries::default();
        }
        Ok(())
    }
}

// Go: the anonymous `struct { Path string; Data string }` in WriteFile
// (tsgo#4699).
#[derive(Debug)]
struct WriteFilePayload {
    path: String,
    data: String,
}

impl MarshalerTo for WriteFilePayload {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "path", &self.path)?;
        marshal_field(enc, &mut first, "data", &self.data)?;
        write_object_end(enc);
        Ok(())
    }
}

impl CallbackFS {
    // Go: callbackfs.go:70 SetConnection
    // SetConnection sets the RPC connection for callbacks.
    // This must be called after the transport connection is established
    // but before any filesystem operations that need callbacks.
    pub fn set_connection(&self, ctx: &Context, conn: Rc<dyn Conn>) {
        *self.ctx.borrow_mut() = Some(ctx.clone());
        *self.conn.borrow_mut() = Some(conn);
    }

    // Go: callbackfs.go:76 isEnabled
    // isEnabled returns true if the named callback is enabled.
    fn is_enabled(&self, name: &str) -> bool {
        self.enabled_callbacks.get(name).copied().unwrap_or(false)
    }

    // Go: callbackfs.go:81 call
    // call invokes a callback on the client and returns the result.
    // PORT: Go `arg any` is any value that marshals (`AnyValue`).
    fn call(&self, name: &str, arg: impl AnyValue) -> Result<Vec<u8>, GoError> {
        let conn = self.conn.borrow().clone();
        let Some(conn) = conn else {
            return Err(errors::new(format!(
                "CallbackFS: {name} called before connection set"
            )));
        };

        // PORT: Go passes the nil `fs.ctx` only when conn is nil too, which
        // returned above.
        let ctx = self
            .ctx
            .borrow()
            .clone()
            .expect("CallbackFS: ctx is set with conn");
        let result = conn.call(&ctx, name, Some(Box::new(arg)))?;
        Ok(result.0)
    }
}

// PORT: Go panics with the error value; the panic message is its text.
fn panic_error(err: &GoError) -> ! {
    panic!("{}", err.error())
}

impl Fs for CallbackFS {
    // Go: callbackfs.go:94 UseCaseSensitiveFileNames
    // UseCaseSensitiveFileNames implements vfs.FS.
    fn use_case_sensitive_file_names(&self) -> bool {
        self.base.use_case_sensitive_file_names()
    }

    // Go: callbackfs.go:104 ReadFile
    // ReadFile implements vfs.FS.
    //
    // The readFile callback uses a wrapped response format to distinguish three states:
    //   - undefined (fall back to real FS): null or empty on wire
    //   - null (not found, no fallback): {"content": null}
    //   - string content: {"content": "..."}
    fn read_file(&self, path: &str) -> (String, bool) {
        if self.is_enabled(CALLBACK_READ_FILE) {
            let result = match self.call(CALLBACK_READ_FILE, path.to_string()) {
                Ok(result) => result,
                Err(err) => panic_error(&err),
            };
            if !result.is_empty() && result != b"null" {
                let mut wrapper = ReadFileWrapper::default();
                if let Err(err) = json_unmarshal(&result, &mut wrapper, &[]) {
                    panic_error(&errors::from_value(err));
                }
                let Some(content) = wrapper.content else {
                    return (String::new(), false);
                };
                return (content, true);
            }
        }
        self.base.read_file(path)
    }

    // Go: callbackfs.go:127 FileExists
    // FileExists implements vfs.FS.
    fn file_exists(&self, path: &str) -> bool {
        if self.is_enabled(CALLBACK_FILE_EXISTS) {
            let result = match self.call(CALLBACK_FILE_EXISTS, path.to_string()) {
                Ok(result) => result,
                Err(err) => panic_error(&err),
            };
            if !result.is_empty() && result != b"null" {
                return result == b"true";
            }
        }
        self.base.file_exists(path)
    }

    // Go: callbackfs.go:141 DirectoryExists
    // DirectoryExists implements vfs.FS.
    fn directory_exists(&self, path: &str) -> bool {
        if self.is_enabled(CALLBACK_DIRECTORY_EXISTS) {
            let result = match self.call(CALLBACK_DIRECTORY_EXISTS, path.to_string()) {
                Ok(result) => result,
                Err(err) => panic_error(&err),
            };
            if !result.is_empty() && result != b"null" {
                return result == b"true";
            }
        }
        self.base.directory_exists(path)
    }

    // Go: callbackfs.go:155 GetAccessibleEntries
    // GetAccessibleEntries implements vfs.FS.
    fn get_accessible_entries(&self, path: &str) -> Entries {
        if self.is_enabled(CALLBACK_GET_ACCESSIBLE_ENTRIES) {
            let result = match self.call(CALLBACK_GET_ACCESSIBLE_ENTRIES, path.to_string()) {
                Ok(result) => result,
                Err(err) => panic_error(&err),
            };
            if !result.is_empty() {
                let mut raw_entries: Option<RawEntries> = None;
                if let Err(err) = json_unmarshal(&result, &mut raw_entries, &[]) {
                    panic_error(&errors::from_value(err));
                }
                if let Some(raw_entries) = raw_entries {
                    return Entries {
                        files: raw_entries.files,
                        directories: raw_entries.directories,
                        symlinks: None,
                    };
                }
            }
        }
        self.base.get_accessible_entries(path)
    }

    // Go: callbackfs.go:181 Realpath
    // Realpath implements vfs.FS.
    fn realpath(&self, path: &str) -> String {
        if self.is_enabled(CALLBACK_REALPATH) {
            let result = match self.call(CALLBACK_REALPATH, path.to_string()) {
                Ok(result) => result,
                Err(err) => panic_error(&err),
            };
            if !result.is_empty() && result != b"null" {
                let mut realpath = String::new();
                if let Err(err) = json_unmarshal(&result, &mut realpath, &[]) {
                    panic_error(&errors::from_value(err));
                }
                return realpath;
            }
        }
        self.base.realpath(path)
    }

    // Go: callbackfs.go:202 WriteFile
    // WriteFile implements vfs.FS.
    // PORT: Go returns the callback error; it is `FsError::Other` with its
    // text.
    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        // tsgo#4699
        if self.is_enabled(CALLBACK_WRITE_FILE) {
            let payload = WriteFilePayload {
                path: path.to_string(),
                data: data.to_string(),
            };

            if let Err(err) = self.call(CALLBACK_WRITE_FILE, payload) {
                return Err(FsError::Other(err.error()));
            }
            return Ok(());
        }

        self.base.write_file(path, data)
    }

    // Go: callbackfs.go:204 AppendFile
    // AppendFile implements vfs.FS - always delegates to base (no callback support).
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.base.append_file(path, data)
    }

    // Go: callbackfs.go:209 Remove
    // Remove implements vfs.FS - always delegates to base (no callback support).
    fn remove(&self, path: &str) -> Result<(), FsError> {
        self.base.remove(path)
    }

    // Go: callbackfs.go:214 Chtimes
    // Chtimes implements vfs.FS - always delegates to base (no callback support).
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        self.base.chtimes(path, a_time, m_time)
    }

    // Go: callbackfs.go:219 Stat
    // Stat implements vfs.FS - always delegates to base (no callback support).
    fn stat(&self, path: &str) -> Option<FileInfo> {
        self.base.stat(path)
    }

    // Go: callbackfs.go:224 WalkDir
    // WalkDir implements vfs.FS - always delegates to base (no callback support).
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        self.base.walk_dir(root, walk_fn)
    }
}
