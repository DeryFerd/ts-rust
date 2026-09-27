//! Go `internal/compiler/host.go`: the compiler host that reads and parses
//! source files and resolves project references.

use crate::frontend::prelude::*;

/// Go `compiler.CompilerHost`.
// PORT: Go `FS()` returns the `vfs.FS` interface. This returns a shared
// `Rc<dyn Fs>`, so callers can keep it.
// PORT: Go `*ast.SourceFile` is `Rc<ParsedSourceFile>`. Go `nil` is `None`.
pub trait CompilerHost {
    fn fs(&self) -> Rc<dyn Fs>;
    fn default_library_path(&self) -> String;
    fn get_current_directory(&self) -> String;
    fn trace(&self, msg: &'static Message, args: Vec<String>);
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>>;
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>>;

    /// True when `fs()` shows the plain OS file system (Go `sys.FS()`,
    /// maybe behind `cachedvfs`), so a parse worker thread reads the same
    /// files, directories and bytes as this host. Then the loader can use
    /// what the workers read and resolved.
    // PORT: not in Go. Go reads and resolves on the host in every parse
    // task; here the parse workers use the OS file system of their thread.
    fn is_plain_os_fs(&self) -> bool {
        false
    }
}

/// Go trace callback `func(msg *diagnostics.Message, args ...any)`.
pub type TraceFn = Rc<dyn Fn(&'static Message, Vec<String>)>;

/// Go `compilerHost`.
// PORT: Go unexported type. Other packages only see it through the
// `CompilerHost` interface, so the Rust name is `CompilerHostImpl`.
pub struct CompilerHostImpl {
    current_directory: String,
    fs: Rc<dyn Fs>,
    default_library_path: String,
    // PORT: Go nil interface is `None`.
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: TraceFn,
    /// `fs` is `bundled::is_wrapped_os_fs` (maybe behind the cache).
    plain_os_fs: bool,
}

// Go: host.go:34 NewCachedFSCompilerHost
pub fn new_cached_fs_compiler_host(
    current_directory: &str,
    fs: Rc<dyn Fs>,
    default_library_path: &str,
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: Option<TraceFn>,
) -> Rc<dyn CompilerHost> {
    let plain_os_fs = is_wrapped_os_fs(&fs);
    new_compiler_host_with(
        current_directory,
        cachedvfs_from(fs),
        default_library_path,
        extended_config_cache,
        trace,
        plain_os_fs,
    )
}

// Go: host.go:44 NewCompilerHost
pub fn new_compiler_host(
    current_directory: &str,
    fs: Rc<dyn Fs>,
    default_library_path: &str,
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: Option<TraceFn>,
) -> Rc<dyn CompilerHost> {
    let plain_os_fs = is_wrapped_os_fs(&fs);
    new_compiler_host_with(
        current_directory,
        fs,
        default_library_path,
        extended_config_cache,
        trace,
        plain_os_fs,
    )
}

/// Go `NewCompilerHost` body. `plain_os_fs`: `fs` shows the plain OS file
/// system (`CompilerHost::is_plain_os_fs`).
fn new_compiler_host_with(
    current_directory: &str,
    fs: Rc<dyn Fs>,
    default_library_path: &str,
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: Option<TraceFn>,
    plain_os_fs: bool,
) -> Rc<dyn CompilerHost> {
    // PORT: Go nil func is `None`.
    let trace = trace.unwrap_or_else(|| Rc::new(|_msg: &'static Message, _args: Vec<String>| {}));
    Rc::new(CompilerHostImpl {
        current_directory: current_directory.to_string(),
        fs,
        default_library_path: default_library_path.to_string(),
        extended_config_cache,
        trace,
        plain_os_fs,
    })
}

impl CompilerHost for CompilerHostImpl {
    // Go: host.go:62 (*compilerHost).FS
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }

    // Go: host.go:66 (*compilerHost).DefaultLibraryPath
    fn default_library_path(&self) -> String {
        self.default_library_path.clone()
    }

    // Go: host.go:70 (*compilerHost).GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }

    // Go: host.go:74 (*compilerHost).Trace
    fn trace(&self, msg: &'static Message, args: Vec<String>) {
        (self.trace)(msg, args);
    }

    // Go: host.go:78 (*compilerHost).GetSourceFile
    // PORT: a parse worker may have parsed the file already (`FilesParser`
    // prefetch, `take_prefetched`). The parser takes `&'static str` (node
    // data points into the text), so a file text is leaked for the program
    // lifetime.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        let script_kind = get_script_kind_from_file_name(&opts.file_name);
        let text: &'static str = if self.plain_os_fs {
            // PERF: on the plain OS file system a worker read the same
            // bytes, so the file is read once, as in Go. A bundled lib is
            // its embedded text (what `WrappedFs::read_file` copies).
            match take_prefetched(opts, script_kind, None) {
                Prefetched::Parse(file) => return Some(Rc::new(file)),
                Prefetched::Text(text) => text,
                Prefetched::Nothing => match bundled_text(&opts.file_name) {
                    Some(text) => text,
                    None => {
                        let (text, ok) = self.fs.read_file(&opts.file_name);
                        if !ok {
                            return None;
                        }
                        Box::leak(text.into_boxed_str())
                    }
                },
            }
        } else {
            let (text, ok) = CompilerHost::fs(self).read_file(&opts.file_name);
            if !ok {
                return None;
            }
            // Another file system can show other bytes than the worker's
            // OS file system, so a worker result is used only for the same
            // text.
            match take_prefetched(opts, script_kind, Some(text.as_str())) {
                Prefetched::Parse(file) => return Some(Rc::new(file)),
                Prefetched::Text(worker_text) => worker_text,
                Prefetched::Nothing => Box::leak(text.into_boxed_str()),
            }
        };
        Some(Rc::new(parse_source_file(opts, text, script_kind)))
    }

    // Go: host.go:86 (*compilerHost).GetResolvedProjectReference
    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>> {
        let (command_line, _) = get_parsed_command_line_of_config_file_path(
            file_name,
            path.clone(),
            None,
            None, /*optionsRaw*/
            self,
            self.extended_config_cache.as_deref(),
        );
        command_line.map(Into::into)
    }

    fn is_plain_os_fs(&self) -> bool {
        self.plain_os_fs
    }
}

// PORT: Go passes the `*compilerHost` as a `tsoptions.ParseConfigHost`
// (it has `FS()` and `GetCurrentDirectory()`). Rust needs the explicit impl.
impl ParseConfigHost for CompilerHostImpl {
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }

    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }
}
