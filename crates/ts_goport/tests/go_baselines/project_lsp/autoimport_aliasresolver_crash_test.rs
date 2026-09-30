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
use ts_goport::gostd::context;
use ts_goport::ls::autoimport::aliasresolver::{
    AliasResolver, bind_alias_resolver_source_file, new_alias_resolver,
};
use ts_goport::ls::autoimport::registry::{DISCARD_ON_CANCEL_KEY, ProjectID, RegistryCloneHost};
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
    fn get_default_project(&self, _path: &Path) -> (Option<ProjectID>, Option<Rc<NewProgram>>) {
        (None, None)
    }
    fn get_program_for_project(&self, _project_id: &ProjectID) -> Option<Rc<NewProgram>> {
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

/// The setup of Go's test (aliasresolver_crash_test.go:47 to :67): an
/// alias resolver over one parsed and bound file with a type error. Returns
/// the resolver and the file.
fn alias_resolver_with_type_error() -> (Rc<AliasResolver>, Node) {
    const FILE_NAME: &str = "/pkg/index.ts";
    let text: &'static str =
        "declare function f(arg: { a: string }): () => void;\nexport const x = f({ a: 1 });\n";

    let (_, fs) = projecttestutil::wrapped_map_fs(
        files(&[(FILE_NAME, text)]),
        true, /*useCaseSensitiveFileNames*/
    );
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
    // Go: module.NewResolver(host, core.EmptyCompilerOptions, "", "", nil)
    let resolver = module::new_resolver(
        resolution_host,
        Rc::new(CompilerOptions::default()),
        "",
        "",
        Vec::new(),
    );
    let r = new_alias_resolver(
        vec![root],
        FxHashMap::default(),
        host,
        Rc::new(resolver),
        Rc::new(|f: &str| Path(f.to_string())),
        Rc::new(|_: &dyn HasFileName, _: &str| {}),
    );
    (r, root)
}

child_test! {
    // Go: aliasresolver_crash_test.go:44 TestAliasResolverGetDiagnosticsDoesNotPanic
    // Regression test for microsoft/typescript-go#4322.
    //
    // During auto-import export extraction, the checker is built on top of an
    // aliasResolver standing in for a real program. This file has a type error, and
    // extracting exports should still complete without crashing.
    fn alias_resolver_get_diagnostics_does_not_panic() {
        let (r, root) = alias_resolver_with_type_error();

        let (ch, _scope) = r.new_checker(&bg(), &[]).expect("checker");

        // Type-checking this file's diagnostics must not panic.
        ch.borrow_mut().get_diagnostics_exported(&bg(), root);
    }
}

child_test! {
    // PORT: no Go counterpart. The file walk of `new_checker` stops on a
    // cancelled context only in a build marked `DISCARD_ON_CANCEL_KEY` (the
    // auto-import warm, which drops its clone on cancel). Any other build
    // keeps Go's behavior: Go's NewChecker has no context.
    fn alias_resolver_walk_stops_only_for_a_discarded_build() {
        let (r, _) = alias_resolver_with_type_error();
        let (canceled, cancel) = context::with_cancel(&bg());
        cancel();

        let discarded = context::with_value(&canceled, &DISCARD_ON_CANCEL_KEY, ());
        assert!(r.new_checker(&discarded, &[]).is_none());
        assert!(r.checker_program.get().is_none(), "a stopped walk makes no program");

        assert!(r.new_checker(&canceled, &[]).is_some());
    }
}
