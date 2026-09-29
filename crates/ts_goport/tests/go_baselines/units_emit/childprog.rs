//! Programs on a map file system, for the tests that build one.
//!
//! PORT: Go tests make any number of programs in one process. In the port a
//! program's parse threads read the OS file system (`osvfs_fs()`), which a
//! test process replaces once (`install_os_override`), and the current
//! program is process state. So each test that builds a program runs in a
//! child process of its own (`in_child`) and installs the override for its
//! map file system there.

use crate::support::child::run_test_in_child;
use crate::support::vfstest::MapFs;
use std::sync::Arc;
use ts_goport::frontend::bundled;
use ts_goport::frontend::compiler::{NewProgram, ProgramOptions, new_compiler_host};
use ts_goport::frontend::parser::ParsedSourceFile;
use ts_goport::frontend::tsoptions::{ParsedCommandLine, ParsedOptions};
use ts_goport::frontend::vfs::{Fs, OsOverride, install_os_override};
use ts_goport::prelude::*;
use ts_goport::program::ls_program;

/// Runs `body` in a child process of its own. `module_path` is the
/// `module_path!()` of the test and `name` its function name.
pub(crate) fn in_child(module_path: &str, name: &str, body: impl FnOnce() + Send + 'static) {
    // libtest names have no crate name.
    let module = module_path.split_once("::").map_or("", |(_, rest)| rest);
    run_test_in_child(&format!("{module}::{name}"), body);
}

/// Makes `map_fs` the OS file system and `cwd` the OS current directory of
/// this process (a child of `in_child`).
pub(crate) fn install_map_fs(map_fs: &MapFs, cwd: &str) {
    let shared = map_fs.clone();
    install_os_override(OsOverride {
        fs: Arc::new(move || -> Rc<dyn Fs> { shared.fs() }),
        current_directory: cwd.to_string(),
    });
}

/// Go `compiler.NewProgram(compiler.ProgramOptions{Config:
/// &tsoptions.ParsedCommandLine{ParsedConfig: &core.ParsedOptions{FileNames:
/// fileNames, CompilerOptions: options}}, Host: compiler.NewCompilerHost(cwd,
/// bundled.WrapFS(fs), bundled.LibPath(), nil, nil)})`.
pub(crate) fn new_program(
    fs: Rc<dyn Fs>,
    cwd: &str,
    file_names: &[&str],
    options: CompilerOptions,
) -> Rc<NewProgram> {
    let config = ParsedCommandLine {
        parsed_config: ParsedOptions {
            compiler_options: Rc::new(options),
            file_names: file_names.iter().map(|name| name.to_string()).collect(),
            ..Default::default()
        },
        ..Default::default()
    };
    new_program_with_config(fs, cwd, Rc::new(config))
}

/// `new_program` with a parsed config.
pub(crate) fn new_program_with_config(
    fs: Rc<dyn Fs>,
    cwd: &str,
    config: Rc<ParsedCommandLine>,
) -> Rc<NewProgram> {
    let host = new_compiler_host(
        cwd,
        bundled::wrap_fs(fs),
        &bundled::lib_path(),
        None,
        None,
        None,
    );
    ls_program::new_program(
        ProgramOptions {
            host,
            config,
            use_source_of_project_reference: false,
            single_threaded: Tristate::Unknown,
            typings_location: String::new(),
            project_name: String::new(),
        },
        None,
    )
}

/// Go `p.GetSourceFile(fileName)`.
pub(crate) fn source_file(p: &NewProgram, file_name: &str) -> Rc<ParsedSourceFile> {
    p.get_source_file(file_name)
        .unwrap_or_else(|| panic!("program has no file {file_name}"))
}
