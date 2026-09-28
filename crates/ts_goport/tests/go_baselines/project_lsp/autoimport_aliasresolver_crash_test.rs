//! Port of Go `internal/ls/autoimport/aliasresolver_crash_test.go`.

use std::rc::Rc;

use rustc_hash::FxHashMap;
use ts_goport::core::Node;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::compiler::NewProgram;
use ts_goport::frontend::core_ext::HasFileName;
use ts_goport::frontend::module;
use ts_goport::frontend::packagejson::InfoCacheEntry;
use ts_goport::frontend::parser::{SourceFileParseOptions, parse_source_file};
use ts_goport::frontend::tspath::Path;
use ts_goport::frontend::vfs::Fs;
use ts_goport::ls::autoimport::aliasresolver::{
    bind_alias_resolver_source_file, new_alias_resolver,
};
use ts_goport::ls::autoimport::registry::RegistryCloneHost;
use ts_goport::options::CompilerOptions;

use super::projecttestutil::{self, files};
use super::util::bg;

// Go: aliasresolver_crash_test.go:19 fakeCloneHost
struct FakeCloneHost {
    fs: Rc<dyn Fs>,
}

impl module::ResolutionHost for FakeCloneHost {
    fn fs(&self) -> &dyn Fs {
        &*self.fs
    }
    fn get_current_directory(&self) -> &str {
        "/"
    }
}

impl RegistryCloneHost for FakeCloneHost {
    fn get_default_project(&self, _path: &Path) -> (Path, Option<&'static NewProgram>) {
        (Path(String::new()), None)
    }
    fn get_program_for_project(&self, _project_path: &Path) -> Option<&'static NewProgram> {
        None
    }
    fn get_package_json(&self, _file_name: &str) -> Option<Rc<InfoCacheEntry>> {
        None
    }
    fn get_source_file(&self, _file_name: &str, _path: &Path) -> Node {
        Node::NIL
    }
    fn dispose(&self) {}
}

child_test! {
    // Go: aliasresolver_crash_test.go:44 TestAliasResolverGetDiagnosticsDoesNotPanic
    // Regression test for microsoft/typescript-go#4322.
    //
    // During auto-import export extraction, the checker is built on top of an
    // aliasResolver standing in for a real program. This file has a type error, and
    // extracting exports should still complete without crashing.
    fn alias_resolver_get_diagnostics_does_not_panic() {
        const FILE_NAME: &str = "/pkg/index.ts";
        let text: &'static str =
            "declare function f(arg: { a: string }): () => void;\nexport const x = f({ a: 1 });\n";

        let (_, fs) = projecttestutil::wrapped_map_fs(files(&[(FILE_NAME, text)]), true /*useCaseSensitiveFileNames*/);
        let host = Rc::new(FakeCloneHost { fs });

        let source_file = Rc::new(parse_source_file(
            &SourceFileParseOptions {
                file_name: FILE_NAME.to_string(),
                path: Path(FILE_NAME.to_string()),
                ..Default::default()
            },
            text,
            ScriptKind::TS,
        ));
        // PORT: a parsed file reaches a program version only after
        // `note_parsed_source_file` (the parse cache calls it; Go needs no step).
        ts_goport::program::note_parsed_source_file(&source_file);
        let root = source_file.root;
        bind_alias_resolver_source_file("/", root);

        let resolution_host: Rc<dyn module::ResolutionHost> = host.clone();
        let resolver = module::new_resolver(resolution_host, Rc::new(CompilerOptions::default()), "", "");
        let r = new_alias_resolver(
            vec![root],
            FxHashMap::default(),
            host,
            Rc::new(resolver),
            Rc::new(|f: &str| Path(f.to_string())),
            Rc::new(|_: &dyn HasFileName, _: &str| {}),
        );

        let (ch, _scope) = r.new_checker(&[]);

        // Type-checking this file's diagnostics must not panic.
        ch.borrow_mut().get_diagnostics_exported(&bg(), root);
    }
}
