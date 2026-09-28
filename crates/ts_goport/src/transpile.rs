//! Go package `transpile` (#4849): single-file JavaScript and declaration
//! emit.
//!
//! PORT: Go makes a program of one file over a `vfstest.FromMap` file
//! system and emits it. Here that program is a program version of the
//! process (`program::new_program_version`, as the compiler runner makes
//! its programs). It is read inside `core::enter_program`, and its checker
//! and emit pools are freed after the emit (`program::release_program`).
//! Its file versions stay leaked, like those of every program version, so
//! the file nodes of the result diagnostics stay valid.

use crate::prelude::*;

use std::sync::{Arc, Mutex, PoisonError};
use std::time::SystemTime;

use crate::emitter::emitter::EmitOnly;
use crate::emitter::program_emit::{self, EmitOptions, WriteFile, WriteFileData};
use crate::frontend::compiler::{NewProgram, ProgramOptions, new_compiler_host};
use crate::frontend::tsoptions::{ParsedCommandLine, ParsedOptions, get_default_lib_file_name};
use crate::frontend::tspath::{
    combine_paths, get_base_file_name, get_directory_path, get_normalized_absolute_path,
    is_rooted_disk_path, normalize_path, remove_trailing_directory_separator,
};
use crate::frontend::vfs::{Entries, FileInfo, FileMode, Fs, FsError, WalkDirFunc, split_path};
use crate::gostd::Context;
use crate::gostd::strconv::quote;
use crate::program;

// Go: transpile/transpile.go:18 Options
/// Options configures single-file transpilation.
// PORT: Go `CompilerOptions *core.CompilerOptions` is an owned value. The
// Go worker clones it, so the caller's options stay unchanged either way.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// CompilerOptions are the base compiler options to use for the transpilation.
    /// If nil, a default set of compiler options is used. Regardless of what is
    /// provided, a number of options are unconditionally overridden; see
    /// [`transpile_module`] and [`transpile_declaration`].
    pub compiler_options: Option<CompilerOptions>,

    /// FileName is the name given to the synthesized input file. It only needs to
    /// be provided if the source text relies on characteristics implied by the
    /// file's extension or path, e.g. its extension controls whether the file is
    /// parsed as a script or module, whether JSX syntax is allowed, etc.
    /// Defaults to "module.ts", or "module.tsx" if CompilerOptions.Jsx is set.
    pub file_name: String,

    /// ReportDiagnostics indicates whether syntactic and compiler option
    /// diagnostics should be included in the result. Regardless of this setting,
    /// diagnostics produced while emitting (including declaration emit errors
    /// such as those produced by isolated declarations) are always included.
    pub report_diagnostics: bool,
}

// Go: transpile/transpile.go:40 Output
/// Output contains the emitted text and any requested diagnostics.
// PORT: an empty `diagnostics` is also the Go nil slice.
#[derive(Clone, Debug, Default)]
pub struct Output {
    pub output_text: String,
    pub diagnostics: Vec<Diagnostic>,
    pub source_map_text: String,
}

// Go: transpile/transpile.go:48 inputDirectory
// inputDirectory is the synthetic current directory used to root the
// single input file created for transpilation.
const INPUT_DIRECTORY: &str = "/";

// Go: transpile/transpile.go:52 libDirectory
// libDirectory is the synthetic directory that the barebones default library
// file is placed in for declaration transpilation. See [barebonesLibContent].
const LIB_DIRECTORY: &str = "/lib";

// Go: transpile/transpile.go:60 barebonesLibContent
// Declaration emit works without a `lib`, but some local inferences you'd
// expect to work won't without at least a minimal `lib` available, since the
// checker will type inferred declarations as `any` without these defined.
// Late bound symbol names, in particular, are impossible to define without
// `Symbol` at least partially defined.
// TODO: This should *probably* just load the full, real `lib` for the target.
const BAREBONES_LIB_CONTENT: &str = r"interface Boolean {}
interface Function {}
interface CallableFunction {}
interface NewableFunction {}
interface IArguments {}
interface Number {}
interface Object {}
interface RegExp {}
interface String {}
interface Array<T> { length: number; [n: number]: T; }
interface SymbolConstructor {
    (desc?: string | number): symbol;
    for(name: string): symbol;
    readonly toStringTag: symbol;
}
declare var Symbol: SymbolConstructor;
interface Symbol {
    readonly [Symbol.toStringTag]: string;
}";

// Go: transpile/transpile.go:93 TranspileModule
/// TranspileModule transpiles a single file of source text to JavaScript
/// using the specified options. If no compiler options are provided, a
/// default set of compiler options is used. It returns nil if the context is
/// canceled before emission completes.
///
/// Extra compiler options that are unconditionally used by this function are:
///   - IsolatedModules = true (unless VerbatimModuleSyntax is set, which makes
///     this option redundant)
///   - NoCheck = true
///   - NoResolve = true
///   - NoLib = true
///   - Declaration = false
///   - DeclarationMap = false
pub fn transpile_module(ctx: &Context, input: &str, options: Options) -> Option<Output> {
    transpile_worker(ctx, input, options, false /*declaration*/)
}

// Go: transpile/transpile.go:114 TranspileDeclaration
/// TranspileDeclaration creates a declaration (.d.ts) file from a single file
/// of source text using the specified options. If no compiler options are
/// provided, a default set of compiler options is used.
///
/// Note that, because only the single input file is available, the resulting
/// declaration file may differ from the one a full program type-check and
/// emit would produce.
///
/// Extra compiler options that are unconditionally used by this function are:
///   - IsolatedModules = true (unless VerbatimModuleSyntax is set, which makes
///     this option redundant)
///   - NoCheck = true
///   - NoResolve = true
///   - NoLib = false
///   - Declaration = true
///   - EmitDeclarationOnly = true
///   - IsolatedDeclarations = true
pub fn transpile_declaration(ctx: &Context, input: &str, options: Options) -> Option<Output> {
    transpile_worker(ctx, input, options, true /*declaration*/)
}

/// The texts that the emit writes (Go `outputText`, `hasOutputText`,
/// `sourceMapText` and `hasSourceMapText`). `None` is "not written".
#[derive(Default)]
struct Written {
    output_text: Option<String>,
    source_map_text: Option<String>,
}

// Go: transpile/transpile.go:118 transpileWorker
fn transpile_worker(
    ctx: &Context,
    input: &str,
    options: Options,
    declaration: bool,
) -> Option<Output> {
    let mut opts = options.compiler_options.unwrap_or_default();

    // Clear options that do not apply to single-file transpilation.
    opts.incremental = Tristate::Unknown;
    opts.declaration = Tristate::Unknown;
    opts.emit_declaration_only = Tristate::Unknown;
    opts.no_emit = Tristate::Unknown;
    opts.lib = None;
    opts.out_file = String::new();
    opts.composite = Tristate::Unknown;
    opts.ts_build_info_file = String::new();
    opts.paths = None;
    opts.root_dirs = None;
    opts.types = None;
    opts.allow_importing_ts_extensions = Tristate::Unknown;
    opts.no_emit_on_error = Tristate::Unknown;
    opts.declaration_dir = String::new();

    // Do not set `isolatedModules` if `verbatimModuleSyntax` was supplied, since
    // it would be redundant.
    if !opts.verbatim_module_syntax.is_true() {
        opts.isolated_modules = Tristate::True;
    }
    opts.no_check = Tristate::True;
    opts.no_resolve = Tristate::True;

    // transpileModule/transpileDeclaration do not write anything to disk, so
    // there's no need to verify there are no conflicts between input and
    // output paths.
    opts.suppress_output_path_check = Tristate::True;

    // FileName can be a non-ts file.
    opts.allow_non_ts_extensions = Tristate::True;

    if declaration {
        opts.declaration = Tristate::True;
        opts.emit_declaration_only = Tristate::True;
        opts.isolated_declarations = Tristate::True;
    } else {
        opts.declaration = Tristate::False;
        opts.declaration_map = Tristate::False;
    }

    // When transpiling declarations, we need a lib. GetDefaultLibFileName will
    // cause the barebones lib below to be used instead of a real lib.
    if declaration {
        opts.no_lib = Tristate::False;
    } else {
        opts.no_lib = Tristate::True;
    }

    // If jsx is specified, then treat the file as .tsx.
    let mut file_name = options.file_name;
    if file_name.is_empty() {
        if opts.jsx != JsxEmit::NONE {
            file_name = "module.tsx".to_string();
        } else {
            file_name = "module.ts".to_string();
        }
    }
    let input_file_name = get_normalized_absolute_path(&file_name, INPUT_DIRECTORY);

    let mut files = FxHashMap::default();
    files.insert(input_file_name.clone(), input.to_string());

    // Declaration emit needs a default lib to resolve global types (e.g.
    // `Array`, `Symbol`); plain transpilation sets NoLib so none is read.
    // The default lib name depends on the configured target.
    if declaration {
        let lib_file_name = get_default_lib_file_name(&opts);
        files.insert(
            combine_paths(LIB_DIRECTORY, &[lib_file_name.as_str()]),
            BAREBONES_LIB_CONTENT.to_string(),
        );
    }

    let fs: Rc<dyn Fs> = Rc::new(MapFs::from_map(files));
    // tsgo#4712: the 6th argument is the content mapper project (Go nil).
    let host = new_compiler_host(INPUT_DIRECTORY, fs, LIB_DIRECTORY, None, None, None);

    // tsgo#4712: Go `core.ParsedOptions` moved to `tsoptions.ParsedOptions`.
    let config = Rc::new(ParsedCommandLine {
        parsed_config: ParsedOptions {
            file_names: vec![input_file_name.clone()],
            compiler_options: Rc::new(opts),
            ..ParsedOptions::default()
        },
        ..ParsedCommandLine::default()
    });
    // PORT: Go `compiler.NewProgram`. The frontend program parses with no
    // current program and then becomes a program version.
    let np: &'static NewProgram = {
        let _scope = enter_program(None);
        Box::leak(Box::new(crate::frontend::compiler::new_program(
            ProgramOptions {
                host,
                config,
                use_source_of_project_reference: false,
                single_threaded: Tristate::Unknown,
                typings_location: String::new(),
                project_name: String::new(),
            },
        )))
    };
    let version = program::new_program_version(np, None);

    let output = {
        let _scope = enter_program(Some(version));

        let mut all_diagnostics: Vec<Diagnostic> = Vec::new();
        if options.report_diagnostics {
            let source_file = program::get_source_file(&input_file_name);
            all_diagnostics.extend(program::get_syntactic_diagnostics(source_file));
            all_diagnostics.extend(program::get_config_file_parsing_diagnostics());
            all_diagnostics.extend(program::get_program_diagnostics());
        }

        let mut emit_only = EmitOnly::All;
        if declaration {
            emit_only = EmitOnly::Dts;
        }

        let written: Arc<Mutex<Written>> = Arc::default();
        let write_file: WriteFile = {
            let written = written.clone();
            Arc::new(
                move |file_name: &str,
                      text: &str,
                      _data: &mut WriteFileData|
                      -> Result<(), String> {
                    let mut written = written.lock().unwrap_or_else(PoisonError::into_inner);
                    if file_name.ends_with(".map") {
                        go_assert!(
                            written.source_map_text.is_none(),
                            "Unexpected multiple source map outputs, file: {file_name}"
                        );
                        written.source_map_text = Some(text.to_string());
                    } else {
                        go_assert!(
                            written.output_text.is_none(),
                            "Unexpected multiple outputs, file: {file_name}"
                        );
                        written.output_text = Some(text.to_string());
                    }
                    Ok(())
                },
            )
        };
        // PORT: Go `Program.Emit` returns nil when the emit is not forced
        // and ctx is canceled (after `HandleNoEmitOptions`, which returns
        // nil here: noEmit and noEmitOnError are cleared above). The port's
        // `program_emit::emit` has no context, so the check is here.
        if !declaration && ctx.err().is_some() {
            None
        } else {
            let result = program_emit::emit(EmitOptions {
                emit_only,
                force_emit: declaration,
                write_file: Some(write_file),
                ..EmitOptions::default()
            });

            // Diagnostics produced during emit (e.g. isolated declaration errors) are
            // always included, regardless of ReportDiagnostics.
            all_diagnostics.extend(result.diagnostics);

            let written =
                std::mem::take(&mut *written.lock().unwrap_or_else(PoisonError::into_inner));
            go_assert!(written.output_text.is_some(), "Output generation failed");

            Some(Output {
                output_text: written.output_text.unwrap_or_default(),
                diagnostics: all_diagnostics,
                source_map_text: written.source_map_text.unwrap_or_default(),
            })
        }
    };
    program::release_program(version);
    output
}

// Go: vfs/vfstest/vfstest.go:70 FromMap (useCaseSensitiveFileNames true),
// behind vfs/iovfs/iofs.go:43 From
// PORT: the port's `vfstest` is test code. This is the read side of a Go
// `vfstest.MapFS` with no symlinks, behind `iovfs.From`: the parent
// directories of each file exist, and a read decodes the Go bytes of the
// map value. Nothing writes to it or walks it: emit writes through the
// `WriteFile` callback, and a program with no config file does not walk
// its directories.
struct MapFs {
    /// File text by path.
    files: FxHashMap<String, String>,
    /// The root and the parent directories of each file.
    directories: FxHashSet<String>,
    /// Go `clock.Now()` when the map is made.
    mod_time: SystemTime,
}

impl MapFs {
    // Go: vfs/vfstest/vfstest.go:80 FromMapWithClock
    // PORT: Go checks the paths in sorted order. Only the input file name
    // can fail a check here, so the order does not change the panic.
    fn from_map(files: FxHashMap<String, String>) -> MapFs {
        let mut posix = false;
        let mut windows = false;
        // The `fstest.MapFS` root always exists.
        let mut directories = FxHashSet::default();
        directories.insert("/".to_string());
        for p in files.keys() {
            if !is_rooted_disk_path(p) {
                go_panic(format!("non-rooted path {}", quote(p)));
            }
            if remove_trailing_directory_separator(&normalize_path(p)) != p.as_str() {
                go_panic(format!("non-normalized path {}", quote(p)));
            }
            if p.starts_with('/') {
                posix = true;
            } else {
                windows = true;
            }
            // Go `convertMapFS` makes the missing parent directories.
            let mut dir = get_directory_path(p);
            while directories.insert(dir.clone()) {
                let parent = get_directory_path(&dir);
                if parent == dir {
                    break;
                }
                dir = parent;
            }
        }
        if posix && windows {
            go_panic("mixed posix and windows paths".to_string());
        }
        MapFs {
            files,
            directories,
            mod_time: SystemTime::now(),
        }
    }
}

/// The map key of `path`: the root and the rest of Go `internal.SplitPath`.
/// It panics like Go when `path` is not absolute.
fn map_key(path: &str) -> String {
    let (root, rest) = split_path(path);
    root + &rest
}

impl Fs for MapFs {
    // Go: vfs/iovfs/iofs.go:151 UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        true
    }

    // Go: vfs/iovfs/iofs.go:159 FileExists
    fn file_exists(&self, path: &str) -> bool {
        self.stat(path).is_some_and(|stat| !stat.is_dir())
    }

    // Go: vfs/iovfs/iofs.go:172 ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        match self.files.get(&map_key(path)) {
            Some(text) => (decode_bytes(text), true),
            None => (String::new(), false),
        }
    }

    fn write_file(&self, _path: &str, _data: &str) -> Result<(), FsError> {
        unported!("vfstest.MapFS.WriteFile in transpile")
    }

    fn append_file(&self, _path: &str, _data: &str) -> Result<(), FsError> {
        unported!("vfstest.MapFS.AppendFile in transpile")
    }

    fn remove(&self, _path: &str) -> Result<(), FsError> {
        unported!("vfstest.MapFS.Remove in transpile")
    }

    fn chtimes(
        &self,
        _path: &str,
        _a_time: Option<SystemTime>,
        _m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        unported!("vfstest.MapFS.Chtimes in transpile")
    }

    // Go: vfs/iovfs/iofs.go:155 DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        self.stat(path).is_some_and(|stat| stat.is_dir())
    }

    // Go: vfs/iovfs/iofs.go:163 GetAccessibleEntries
    // PORT: with no symlinks each entry is a file or a directory. Go
    // `fs.ReadDir` sorts the entries by name.
    fn get_accessible_entries(&self, path: &str) -> Entries {
        let dir = map_key(path);
        let mut entries: Vec<(String, bool)> = self
            .files
            .keys()
            .map(|p| (p, false))
            .chain(self.directories.iter().map(|p| (p, true)))
            .filter(|(p, _)| **p != dir && get_directory_path(p) == dir)
            .map(|(p, is_dir)| (get_base_file_name(p), is_dir))
            .collect();
        entries.sort_by(|a, b| compare_go_strings(&a.0, &b.0));
        let mut result = Entries {
            symlinks: Some(FxHashSet::default()),
            ..Entries::default()
        };
        for (name, is_dir) in entries {
            if is_dir {
                result.directories.push(name);
            } else {
                result.files.push(name);
            }
        }
        result
    }

    // Go: vfs/iovfs/iofs.go:167 Stat
    // PORT: only `is_dir` of the mode is read. A file has the `fstest`
    // mode 0; a directory has the mode of vfstest `mkdirAll`.
    fn stat(&self, path: &str) -> Option<FileInfo> {
        let (root, rest) = split_path(path);
        let name = match rest.rsplit('/').next() {
            Some(name) if !name.is_empty() => name.to_string(),
            _ => ".".to_string(),
        };
        let key = root + &rest;
        if let Some(text) = self.files.get(&key) {
            return Some(FileInfo {
                name,
                size: go_string_bytes(text).len() as i64,
                mode: FileMode(0),
                mod_time: Some(self.mod_time),
            });
        }
        if self.directories.contains(&key) {
            return Some(FileInfo {
                name,
                size: 0,
                mode: FileMode::DIR | FileMode(0o755),
                mod_time: Some(self.mod_time),
            });
        }
        None
    }

    fn walk_dir(&self, _root: &str, _walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        unported!("vfstest.MapFS.WalkDir in transpile")
    }

    // Go: vfs/iovfs/iofs.go:190 Realpath
    // PORT: with no symlinks the real path of an entry is its own path. The
    // root is no entry of the Go map, so it keeps `path`, as a missing
    // path does.
    fn realpath(&self, path: &str) -> String {
        let (root, rest) = split_path(path);
        let key = root + &rest;
        if !rest.is_empty() && (self.files.contains_key(&key) || self.directories.contains(&key)) {
            return key;
        }
        path.to_string()
    }
}

// Go: vfs/internal/internal.go:170 decodeBytes
// PORT: the port's copy in `frontend/vfs` is private. This one takes the
// map value, whose Go bytes (`[]byte(content)`) the Go map holds, and
// returns the port form (see `scanner_util::GO_STRING_MARKER`). Go reads
// `len/2` UTF-16 units and ignores an odd last byte; `utf16.Decode` makes
// each unpaired surrogate U+FFFD.
fn decode_bytes(text: &str) -> String {
    let utf16 = |s: &[u8], big_endian: bool| {
        let units = s.chunks_exact(2).map(|pair| {
            if big_endian {
                u16::from_be_bytes([pair[0], pair[1]])
            } else {
                u16::from_le_bytes([pair[0], pair[1]])
            }
        });
        go_string_from_utf8(
            char::decode_utf16(units)
                .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
                .collect(),
        )
    };
    match &*go_string_bytes(text) {
        [0xFF, 0xFE, rest @ ..] => utf16(rest, false),
        [0xFE, 0xFF, rest @ ..] => utf16(rest, true),
        // The UTF-8 BOM (EF BB BF) is U+FEFF in the port form too.
        _ => text.strip_prefix('\u{FEFF}').unwrap_or(text).to_string(),
    }
}
