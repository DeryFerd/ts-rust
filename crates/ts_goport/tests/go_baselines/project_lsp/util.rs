//! Short forms of the Go calls that the project tests repeat. No Go
//! file: each helper is one Go expression (named in its comment).

use std::rc::Rc;

use ts_goport::frontend::compiler::NewProgram;
use ts_goport::gostd::{Context, context};
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program;
use ts_goport::project::Session;

use super::projecttestutil;

/// Go `lsproto.DocumentUri(s)`.
pub fn uri(s: &str) -> lsproto::DocumentUri {
    lsproto::DocumentUri(s.to_string())
}

/// Go `context.Background()`.
pub fn bg() -> Context {
    context::background()
}

/// Go `session.DidOpenFile(ctx, uri, 1, content, lsproto.LanguageKindTypeScript)`.
pub fn open(session: &Rc<Session>, u: &str, content: &str) {
    open_kind(session, u, content, lsproto::LanguageKind::TYPE_SCRIPT);
}

/// Go `session.DidOpenFile(ctx, uri, 1, content, kind)`.
pub fn open_kind(session: &Rc<Session>, u: &str, content: &str, kind: lsproto::LanguageKind) {
    session.did_open_file(&bg(), &uri(u), 1, content, &kind);
}

/// Go `session.DidCloseFile(ctx, uri)`.
pub fn close(session: &Rc<Session>, u: &str) {
    session.did_close_file(&bg(), &uri(u));
}

/// Go `session.GetLanguageService(ctx, uri)` with `assert.NilError`, then
/// `ls.GetProgram()`.
pub fn program(session: &Rc<Session>, u: &str) -> Rc<NewProgram> {
    let ls = session
        .get_language_service(&bg(), &uri(u))
        .unwrap_or_else(|err| panic!("GetLanguageService({u}): {}", err.error()));
    Rc::clone(&ls.program)
}

/// Go `program.GetSourceFile(name) != nil`.
pub fn has_file(p: &NewProgram, name: &str) -> bool {
    p.get_source_file(name).is_some()
}

/// Go `program.GetSourceFile(name).Text()`.
pub fn text(p: &NewProgram, name: &str) -> String {
    p.get_source_file(name)
        .unwrap_or_else(|| panic!("no source file {name}"))
        .text
        .to_string()
}

/// Go `len(program.GetSemanticDiagnostics(projecttestutil.WithRequestID(ctx), program.GetSourceFile(name)))`.
pub fn sem_diag_count(p: &NewProgram, name: &str) -> usize {
    let file = p
        .get_source_file(name)
        .unwrap_or_else(|| panic!("no source file {name}"));
    let ctx = projecttestutil::with_request_id(&bg());
    ls_program::get_semantic_diagnostics(p, &ctx, file.root).len()
}

/// Go `program.CommandLine().ParsedConfig.FileNames`.
pub fn file_names(p: &NewProgram) -> Vec<String> {
    p.command_line().parsed_config.file_names.clone()
}

/// Go `programA == programB`.
pub fn same_program(a: &NewProgram, b: &NewProgram) -> bool {
    std::ptr::eq(a, b)
}

/// Go `session.DidChangeWatchedFiles(ctx, []*lsproto.FileEvent{...})`.
pub fn watch(session: &Rc<Session>, events: &[(lsproto::FileChangeType, &str)]) {
    let events: Vec<lsproto::FileEvent> = events
        .iter()
        .map(|(kind, u)| lsproto::FileEvent {
            uri: uri(u),
            type_: *kind,
        })
        .collect();
    session.did_change_watched_files(&bg(), &events);
}

pub const CREATED: lsproto::FileChangeType = lsproto::FileChangeType::CREATED;
pub const CHANGED: lsproto::FileChangeType = lsproto::FileChangeType::CHANGED;
pub const DELETED: lsproto::FileChangeType = lsproto::FileChangeType::DELETED;

/// Go `lsproto.TextDocumentContentChangePartialOrWholeDocument{Partial: ...}`
/// for the range `start` to `end` (line, character).
pub fn partial(
    start: (u32, u32),
    end: (u32, u32),
    text: &str,
) -> lsproto::TextDocumentContentChangePartialOrWholeDocument {
    lsproto::TextDocumentContentChangePartialOrWholeDocument {
        partial: Some(lsproto::TextDocumentContentChangePartial {
            range: lsproto::Range {
                start: lsproto::Position {
                    line: start.0,
                    character: start.1,
                },
                end: lsproto::Position {
                    line: end.0,
                    character: end.1,
                },
            },
            range_length: None,
            text: text.to_string(),
        }),
        whole_document: None,
    }
}

/// Go `session.DidChangeFile(ctx, uri, version, []...{{Partial: ...}})`.
pub fn edit(
    session: &Rc<Session>,
    u: &str,
    version: i32,
    start: (u32, u32),
    end: (u32, u32),
    text: &str,
) {
    session.did_change_file(&bg(), &uri(u), version, &[partial(start, end, text)]);
}

/// Go `tspath.Path(s)`.
pub fn path(s: &str) -> ts_goport::frontend::tspath::Path {
    ts_goport::frontend::tspath::Path(s.to_string())
}

/// Go `len(session.Snapshot().ProjectCollection.Projects())`.
pub fn projects_len(session: &Rc<Session>) -> usize {
    session.snapshot().project_collection.projects().len()
}

/// Go `snapshot.ProjectCollection.ConfiguredProject(tspath.Path(p)) != nil`.
pub fn has_configured_project(session: &Rc<Session>, p: &str) -> bool {
    session
        .snapshot()
        .project_collection
        .configured_project(&path(p))
        .is_some()
}

/// Go `snapshot.ProjectCollection.InferredProject() != nil`.
pub fn has_inferred_project(session: &Rc<Session>) -> bool {
    session
        .snapshot()
        .project_collection
        .inferred_project()
        .is_some()
}

/// Go `snapshot.ConfigFileRegistry.GetConfig(tspath.Path(p)) != nil`.
pub fn has_config(session: &Rc<Session>, p: &str) -> bool {
    session
        .snapshot()
        .config_file_registry
        .get_config(&path(p))
        .is_some()
}

/// Go `session.GetLanguageService(ctx, uri)` with `assert.NilError`.
pub fn language_service(session: &Rc<Session>, u: &str) -> ts_goport::ls::LanguageService {
    session
        .get_language_service(&bg(), &uri(u))
        .unwrap_or_else(|err| panic!("GetLanguageService({u}): {}", err.error()))
}

/// Go `session.Snapshot().GetDefaultProject(uri).Name()`.
pub fn default_project_name(session: &Rc<Session>, u: &str) -> String {
    session
        .snapshot()
        .get_default_project(&uri(u))
        .unwrap_or_else(|| panic!("no default project for {u}"))
        .borrow()
        .name()
}

/// Go `lsutil.ParseUserPreferences(map[string]any{...})` input: a JSON
/// object literal in Go map form.
pub fn lsp_object(
    entries: Vec<(&str, ts_goport::frontend::json_ext::LspAny)>,
) -> ts_goport::frontend::json_ext::LspAny {
    ts_goport::frontend::json_ext::LspAny::Object(
        entries
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}

/// The `setup` of the Go internal tests (snapshot_test.go:21,
/// refcountcache_test.go:23, ...): `NewSession` on the wrapped map FS
/// with watch and logging off and no client, logger or npm executor.
pub fn bare_session(files: super::projecttestutil::FileMap) -> Rc<Session> {
    use ts_goport::frontend::bundled;
    use ts_goport::project::{self, SessionInit, SessionOptions};
    let (_, fs) = projecttestutil::wrapped_map_fs(files, false /*useCaseSensitiveFileNames*/);
    project::new_session(&SessionInit {
        background_ctx: bg(),
        options: Rc::new(SessionOptions {
            current_directory: "/".to_string(),
            default_library_path: bundled::lib_path(),
            typings_location: "/home/src/Library/Caches/typescript".to_string(),
            position_encoding: lsproto::PositionEncodingKind::UTF8,
            watch_enabled: false,
            logging_enabled: false,
            ..projecttestutil::session_options("/")
        }),
        fs,
        client: None,
        logger: None,
        npm_executor: None,
        parse_cache: None,
    })
}

/// Go `session.GetLanguageService(ctx, uri)` then `ls.GetProgram()`.
pub fn program_of(session: &Rc<Session>, u: &str) -> Rc<NewProgram> {
    program(session, u)
}

/// Go `generateFileEvents(count, pathTemplate, changeType)` (bulkcache_test.go):
/// `%d` in the template is the index.
pub fn generate_file_events(
    count: usize,
    path_template: &str,
    change_type: lsproto::FileChangeType,
) -> Vec<lsproto::FileEvent> {
    (0..count)
        .map(|i| lsproto::FileEvent {
            uri: uri(&path_template.replace("%d", &i.to_string())),
            type_: change_type,
        })
        .collect()
}

/// Go `session.Snapshot().GetDefaultProject(uri).Kind`.
pub fn default_project_kind(session: &Rc<Session>, u: &str) -> ts_goport::project::Kind {
    session
        .snapshot()
        .get_default_project(&uri(u))
        .unwrap_or_else(|| panic!("no default project for {u}"))
        .borrow()
        .kind
}

/// Go `len(program.GetSemanticDiagnostics(ctx, nil))`: every file.
pub fn all_sem_diag_count(p: &NewProgram) -> usize {
    ls_program::get_semantic_diagnostics(p, &bg(), ts_goport::core::Node::NIL).len()
}

/// Go `snapshot.ProjectCollection.ConfiguredProject(tspath.Path(p))`.
pub fn configured_project(
    session: &Rc<Session>,
    p: &str,
) -> Option<Rc<std::cell::RefCell<ts_goport::project::Project>>> {
    session
        .snapshot()
        .project_collection
        .configured_project(&path(p))
}

/// Go `snapshot.GetDefaultProject(uri) == project` (pointer equality).
pub fn default_project_is(
    session: &Rc<Session>,
    u: &str,
    project: &Rc<std::cell::RefCell<ts_goport::project::Project>>,
) -> bool {
    session
        .snapshot()
        .get_default_project(&uri(u))
        .is_some_and(|p| Rc::ptr_eq(&p, project))
}
