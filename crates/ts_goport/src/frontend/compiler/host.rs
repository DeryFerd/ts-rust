//! Go `internal/compiler/host.go`: the compiler host that reads and parses
//! source files and resolves project references.

use crate::prelude::*;

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
    fn get_resolved_project_reference(&self, file_name: &str, path: &Path) -> Option<Rc<ParsedCommandLine>>;
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
}

// Go: host.go:34 NewCachedFSCompilerHost
pub fn new_cached_fs_compiler_host(
    current_directory: &str,
    fs: Rc<dyn Fs>,
    default_library_path: &str,
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: Option<TraceFn>,
) -> Rc<dyn CompilerHost> {
    new_compiler_host(current_directory, cachedvfs_from(fs), default_library_path, extended_config_cache, trace)
}

// Go: host.go:44 NewCompilerHost
pub fn new_compiler_host(
    current_directory: &str,
    fs: Rc<dyn Fs>,
    default_library_path: &str,
    extended_config_cache: Option<Rc<dyn ExtendedConfigCache>>,
    trace: Option<TraceFn>,
) -> Rc<dyn CompilerHost> {
    // PORT: Go nil func is `None`.
    let trace = trace.unwrap_or_else(|| Rc::new(|_msg: &'static Message, _args: Vec<String>| {}));
    Rc::new(CompilerHostImpl {
        current_directory: current_directory.to_string(),
        fs,
        default_library_path: default_library_path.to_string(),
        extended_config_cache,
        trace,
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
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        let (text, ok) = self.fs().read_file(&opts.file_name);
        if !ok {
            return None;
        }
        // PORT: the parser takes `&'static str` (node data points into the
        // text), so the file text is leaked for the program lifetime.
        let text: &'static str = Box::leak(text.into_boxed_str());
        Some(Rc::new(parse_source_file(opts, text, get_script_kind_from_file_name(&opts.file_name))))
    }

    // Go: host.go:86 (*compilerHost).GetResolvedProjectReference
    fn get_resolved_project_reference(&self, file_name: &str, path: &Path) -> Option<Rc<ParsedCommandLine>> {
        let (command_line, _) = get_parsed_command_line_of_config_file_path(
            file_name,
            path,
            None,
            None, /*optionsRaw*/
            self,
            self.extended_config_cache.as_deref(),
        );
        command_line.map(Into::into)
    }
}

// PORT: Go passes the `*compilerHost` as a `tsoptions.ParseConfigHost`
// (it has `FS()` and `GetCurrentDirectory()`). Rust needs the explicit impl.
impl ParseConfigHost for CompilerHostImpl {
    fn fs(&self) -> &dyn Fs {
        &*self.fs
    }

    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }
}
