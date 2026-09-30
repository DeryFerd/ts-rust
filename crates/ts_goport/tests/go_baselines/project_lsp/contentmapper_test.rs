//! Port of Go `internal/project/contentmapper_test.go` (tsgo#4712).
//!
//! PORT: Go `defer session.Close()` is a `session.close()` at the end of
//! each test. The mappers run in-process (`contentmappertest::new_spawner`).
//! Go `projecttestutil.GetSessionInitOptions(files, options, nil)`: a nil
//! `tiOptions` is the default `TypingsInstallerOptions`.

use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Once};

use ts_goport::contentmapper::{self, ProcessExitState};
use ts_goport::frontend::compiler::NewProgram;
use ts_goport::frontend::parser::ParsedSourceFile;
use ts_goport::frontend::vfs::Fs;
use ts_goport::gostd::{GoError, strconv};
use ts_goport::ipc;
use ts_goport::locale;
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program;
use ts_goport::project::{self, Session, SessionInit, SessionOptions};

use super::projecttestutil::{self, FileMap, SessionUtils, TypingsInstallerOptions, files};
use super::util::*;
use crate::support::{contentmappertest, vfstest};

// Go: contentmapper_test.go:27 recordingContentMapperSpawner
// PORT: Go `atomic.Int32` counters. The spawned process wrappers share
// `closes`, so it is an `Arc`.
struct RecordingContentMapperSpawner {
    inner: Rc<dyn contentmapper::Spawner>,
    spawns: AtomicI32,
    closes: Arc<AtomicI32>,
}

impl RecordingContentMapperSpawner {
    /// Go `&recordingContentMapperSpawner{inner: inner}`.
    fn new(inner: Rc<dyn contentmapper::Spawner>) -> Rc<Self> {
        Rc::new(RecordingContentMapperSpawner {
            inner,
            spawns: AtomicI32::new(0),
            closes: Arc::new(AtomicI32::new(0)),
        })
    }

    /// Go `spawner.spawns.Load()`.
    fn spawns(&self) -> i32 {
        self.spawns.load(Ordering::SeqCst)
    }

    /// Go `spawner.closes.Load()`.
    fn closes(&self) -> i32 {
        self.closes.load(Ordering::SeqCst)
    }
}

impl contentmapper::Spawner for RecordingContentMapperSpawner {
    // Go: contentmapper_test.go:33 recordingContentMapperSpawner.Spawn
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        let process = contentmapper::Spawner::spawn(&*self.inner, command, dir, stderr)?;
        self.spawns.fetch_add(1, Ordering::SeqCst);
        Ok(Arc::new(RecordingContentMapperProcess {
            inner: process,
            closes: self.closes.clone(),
            once: Once::new(),
        }))
    }
}

// Go: contentmapper_test.go:42 recordingContentMapperProcess
// PORT: Go embeds the spawned `io.ReadWriteCloser`; the methods forward to
// `inner`.
struct RecordingContentMapperProcess {
    inner: Arc<dyn ProcessExitState>,
    closes: Arc<AtomicI32>,
    once: Once,
}

impl ipc::ReadWriteCloser for RecordingContentMapperProcess {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        ipc::ReadWriteCloser::read(&*self.inner, buf)
    }

    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        ipc::ReadWriteCloser::write(&*self.inner, buf)
    }

    fn flush(&self) -> std::io::Result<()> {
        ipc::ReadWriteCloser::flush(&*self.inner)
    }

    // Go: contentmapper_test.go:48 recordingContentMapperProcess.Close
    fn close(&self) -> Result<(), GoError> {
        self.once.call_once(|| {
            self.closes.fetch_add(1, Ordering::SeqCst);
        });
        ipc::ReadWriteCloser::close(&*self.inner)
    }
}

// Go: the wrapper embeds only `io.ReadWriteCloser`, so it has no
// `ExitCode` method.
impl ProcessExitState for RecordingContentMapperProcess {}

/// Go `&project.SessionOptions{CurrentDirectory: dir, DefaultLibraryPath:
/// bundled.LibPath(), TypingsLocation: projecttestutil.TestTypingsLocation,
/// PositionEncoding: lsproto.PositionEncodingKindUTF8, RunExternalCode:
/// run}`. The other fields are Go zero values.
fn options(current_directory: &str, run_external_code: bool) -> SessionOptions {
    SessionOptions {
        watch_enabled: false,
        logging_enabled: false,
        run_external_code,
        ..projecttestutil::session_options(current_directory)
    }
}

/// Go `projecttestutil.GetSessionInitOptions(files, options, nil)`.
fn init_options(files: FileMap, options: SessionOptions) -> (SessionInit, SessionUtils) {
    projecttestutil::get_session_init_options(
        files,
        Some(options),
        TypingsInstallerOptions::default(),
    )
}

/// Go `GetSessionInitOptions`, then `init.Spawner = spawner` and
/// `project.NewSession(init)`.
fn new_session(
    files: FileMap,
    options: SessionOptions,
    spawner: Rc<dyn contentmapper::Spawner>,
) -> (Rc<Session>, SessionUtils) {
    let (mut init, utils) = init_options(files, options);
    init.spawner = Some(spawner);
    (project::new_session(&init), utils)
}

/// Go `lsproto.LanguageKind("box")`.
fn box_kind() -> lsproto::LanguageKind {
    lsproto::LanguageKind("box".into())
}

/// Go `session.DidChangeFile(ctx, uri, version, []...{{WholeDocument: ...}})`.
fn change_whole(session: &Rc<Session>, u: &str, version: i32, text: &str) {
    session.did_change_file(
        &bg(),
        &uri(u),
        version,
        &[lsproto::TextDocumentContentChangePartialOrWholeDocument {
            partial: None,
            whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                text: text.to_string(),
            }),
        }],
    );
}

/// Go `&lsproto.FileEvent{Uri: uri, Type: kind}`.
fn file_event(u: &str, kind: lsproto::FileChangeType) -> lsproto::FileEvent {
    lsproto::FileEvent {
        uri: uri(u),
        type_: kind,
    }
}

/// Go `utils.FS().WriteFile(path, content)` with `assert.NilError`.
fn write_file(utils: &SessionUtils, path: &str, content: &str) {
    Fs::write_file(&**utils.fs(), path, content)
        .unwrap_or_else(|err| panic!("WriteFile({path}): {err:?}"));
}

/// Go `program.GetSourceFile(name)`, which must not be nil.
fn source_file(program: &NewProgram, name: &str) -> Rc<ParsedSourceFile> {
    program
        .get_source_file(name)
        .unwrap_or_else(|| panic!("expected {name} in the program"))
}

/// Go `session.Snapshot().GetDefaultProject(uri)`, which must not be nil.
fn default_project(session: &Rc<Session>, u: &str) -> Rc<RefCell<project::Project>> {
    session
        .snapshot()
        .get_default_project(&uri(u))
        .unwrap_or_else(|| panic!("expected a default project for {u}"))
}

/// Go `_, err = session.GetLanguageService(ctx, uri)` and
/// `assert.ErrorContains(t, err, "no project found")`.
fn assert_no_project(session: &Rc<Session>, u: &str) {
    match session.get_language_service(&bg(), &uri(u)) {
        Ok(_) => panic!("expected no project for {u}"),
        Err(err) => assert!(err.error().contains("no project found"), "{}", err.error()),
    }
}

/// The `project.ContentMapperContributions` literal of the Go tests: the
/// transforming mapper for `.box`, contributed by `test.extension`.
fn box_contributions(package_directory: &str) -> project::ContentMapperContributions {
    project::ContentMapperContributions {
        mappers: vec![Rc::new(contentmapper::Mapper {
            definition: contentmapper::Definition {
                package: "test.extension".to_string(),
                extensions: vec![".box".to_string()],
                ..Default::default()
            },
            manifest: contentmapper::Manifest {
                name: "mapper".to_string(),
                version: "1.0.0".to_string(),
                exec: vec![contentmappertest::TRANSFORMING_MAPPER.to_string()],
                compiler_options: contentmappertest::DECLARED_OPTIONS
                    .iter()
                    .map(|option| (*option).to_string())
                    .collect(),
                ..Default::default()
            },
            package_directory: package_directory.to_string(),
            contribution_id: "test.extension[0]".to_string(),
        })],
        extensions: vec![".box".to_string()],
    }
}

const MAIN_URI: &str = "file:///home/project/main.ts";
const BOX_URI: &str = "file:///home/project/app.box";
const BOX_PATH: &str = "/home/project/app.box";
const BOX_TEXT: &str = "export const version = #{target};\n";

// ---------------------------------------------------------------------------
// TestContentMapperProjectWithoutMappedFiles, TestContentMapperParallelFileLoading (ts#64221)
// ---------------------------------------------------------------------------

/// Go `&project.SessionOptions{CurrentDirectory: "/home/project",
/// DefaultLibraryPath: bundled.LibPath(), PositionEncoding:
/// lsproto.PositionEncodingKindUTF8, RunExternalCode: true}` (no typings
/// location).
fn race_options() -> SessionOptions {
    SessionOptions {
        typings_location: String::new(),
        ..options("/home/project", true)
    }
}

// Go: contentmapper_test.go:53 TestContentMapperProjectWithoutMappedFiles
fn content_mapper_project_without_mapped_files(has_mapper: bool) {
    let mut config = r#"{"compilerOptions": {"noLib": true}}"#;
    if has_mapper {
        config = r#"{
					"compilerOptions": { "noLib": true },
					"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
				}"#;
    }
    let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
    let file_map = files(&[
        ("/home/project/tsconfig.json", config),
        (
            "/home/project/node_modules/mapper/package.json",
            mapper.as_str(),
        ),
        ("/home/project/main.ts", "export {};"),
    ]);
    let (mut init, _utils) = init_options(file_map, race_options());
    let spawner = RecordingContentMapperSpawner::new(contentmappertest::new_spawner());
    let spawner_for_init: Rc<dyn contentmapper::Spawner> = spawner.clone();
    init.spawner = Some(spawner_for_init);
    let session = project::new_session(&init);

    let ctx = bg();
    session.did_open_file(
        &ctx,
        &uri(MAIN_URI),
        1,
        "export {};",
        &lsproto::LanguageKind::TYPE_SCRIPT,
    );
    let language_service = session
        .get_language_service(&ctx, &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("GetLanguageService: {}", err.error()));
    // Access after freezing must not try to initialize using the cleared builder.
    let program = language_service.get_program();
    let mapper_project = program.content_mapper_project();
    assert_eq!(mapper_project.is_some(), has_mapper);
    let again = program.content_mapper_project();
    assert_eq!(
        again.as_ref().map(|p| Rc::as_ptr(p) as *const u8),
        mapper_project.as_ref().map(|p| Rc::as_ptr(p) as *const u8)
    );
    assert_eq!(spawner.spawns(), 0);
    session.close();
}

child_test! {
    // Go: contentmapper_test.go:56 TestContentMapperProjectWithoutMappedFiles/hasMapper=false
    fn content_mapper_project_without_mapped_files_has_mapper_false() {
        content_mapper_project_without_mapped_files(false);
    }
}

child_test! {
    // Go: contentmapper_test.go:56 TestContentMapperProjectWithoutMappedFiles/hasMapper=true
    fn content_mapper_project_without_mapped_files_has_mapper_true() {
        content_mapper_project_without_mapped_files(true);
    }
}

child_test! {
    // Go: contentmapper_test.go:95 TestContentMapperParallelFileLoading
    fn content_mapper_parallel_file_loading() {
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let mut entries: Vec<(String, String)> = vec![
            (
                "/home/project/tsconfig.json".to_string(),
                r#"{
			"compilerOptions": { "target": "es2020", "noLib": true },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#
                .to_string(),
            ),
            ("/home/project/node_modules/mapper/package.json".to_string(), mapper.clone()),
            ("/home/project/main.ts".to_string(), "export {};".to_string()),
        ];
        // Parallel parsing reads the mapper project identity while another file initializes it.
        const FILE_COUNT: usize = 32;
        for i in 0..FILE_COUNT {
            entries.push((
                format!("/home/project/file{i}.box"),
                "export const version = #{target};\n".to_string(),
            ));
        }
        let borrowed: Vec<(&str, &str)> =
            entries.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();
        let (mut init, _utils) = init_options(files(&borrowed), race_options());
        init.spawner = Some(contentmappertest::new_spawner());
        let session = project::new_session(&init);

        let ctx = bg();
        session.did_open_file(&ctx, &uri(MAIN_URI), 1, "export {};", &lsproto::LanguageKind::TYPE_SCRIPT);
        let language_service = session
            .get_language_service(&ctx, &uri(MAIN_URI))
            .unwrap_or_else(|err| panic!("GetLanguageService: {}", err.error()));
        let program = language_service.get_program();
        let mapper_project = program.content_mapper_project().expect("mapper project");
        let again = program.content_mapper_project().expect("mapper project");
        assert!(Rc::ptr_eq(&again, &mapper_project));
        for i in 0..FILE_COUNT {
            let file_name = format!("/home/project/file{i}.box");
            let file = program
                .get_source_file(&file_name)
                .unwrap_or_else(|| panic!("expected {file_name} to be loaded"));
            assert_eq!(
                file.text,
                "const __VERSION = \"1.0.0\";\nexport const version = 7;\n"
            );
        }
        session.close();
    }
}

// ---------------------------------------------------------------------------
// TestContentMapperInProject
// ---------------------------------------------------------------------------

const IN_PROJECT_MAIN: &str =
    "import { version } from \"./app.box\";\nexport const twice: number = version * 2;\n";

// Go: contentmapper_test.go:55 TestContentMapperInProject files
fn in_project_files() -> FileMap {
    let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
    files(&[
        (
            "/home/project/tsconfig.json",
            r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": true },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
        ),
        (
            "/home/project/node_modules/mapper/package.json",
            mapper.as_str(),
        ),
        ("/home/project/app.box", BOX_TEXT),
        ("/home/project/main.ts", IN_PROJECT_MAIN),
    ])
}

// Go: contentmapper_test.go:65 TestContentMapperInProject newSession
fn in_project_session(trusted: bool) -> (Rc<Session>, SessionUtils) {
    new_session(
        in_project_files(),
        SessionOptions {
            logging_enabled: true,
            ..options("/home/project", trusted)
        },
        contentmappertest::new_spawner(),
    )
}

child_test! {
    // Go: contentmapper_test.go:78 TestContentMapperInProject/trusted workspace transforms the content-mapped file
    fn trusted_workspace_transforms_the_content_mapped_file() {
        let (session, utils) = in_project_session(true);

        open(&session, MAIN_URI, IN_PROJECT_MAIN);
        let main_program = program(&session, MAIN_URI);

        let box_file = main_program
            .get_source_file(BOX_PATH)
            .expect("expected app.box to be loaded into the program");
        // The #{target} token was substituted with the es2020 target value (7) by the content mapper.
        assert!(
            box_file.text.contains("export const version = 7;"),
            "app.box was not transformed: {:?}",
            box_file.text
        );

        // The config's .box mapper should have been registered for text document synchronization.
        session.wait_for_background_tasks();
        let calls = utils.client().register_content_mapper_extensions_calls();
        assert!(!calls.is_empty(), "expected RegisterContentMapperExtensions to be called");
        assert_eq!(calls.last().cloned(), Some(vec![".box".to_string()]));
        // ts#64015 removed the log assertions here.
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:103 TestContentMapperInProject/untrusted workspace does not run the content mapper
    fn untrusted_workspace_does_not_run_the_content_mapper() {
        let (session, utils) = in_project_session(false);

        open(&session, MAIN_URI, IN_PROJECT_MAIN);
        let main_program = program(&session, MAIN_URI);

        // Without workspace trust, the content mapper gate drops the mappers, so .box is not a recognized
        // extension and app.box never enters the program.
        assert!(
            main_program.get_source_file(BOX_PATH).is_none(),
            "app.box should not be loaded without trust"
        );

        // No content mapper extensions should be registered without trust.
        session.wait_for_background_tasks();
        for call in utils.client().register_content_mapper_extensions_calls() {
            assert!(
                call.is_empty(),
                "expected no content mapper extensions to be registered without trust"
            );
        }
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:124 TestContentMapperInProject/editing an open content-mapped file reparses it through the mapper
    fn editing_an_open_content_mapped_file_reparses_it_through_the_mapper() {
        let (session, _utils) = in_project_session(true);

        open(&session, MAIN_URI, IN_PROJECT_MAIN);
        // Open the .box with its content-mapped language id so its overlay script kind is Unknown, matching how an
        // editor opens a content-mapped file. This is what made the incremental reparse panic.
        open_kind(&session, BOX_URI, BOX_TEXT, box_kind());
        program(&session, MAIN_URI);

        // Editing the open .box file drives the single-file incremental reparse path
        // (Program.UpdateProgram), which must re-run the content mapper transform rather than parse the
        // raw source text.
        change_whole(
            &session,
            BOX_URI,
            2,
            "export const version = #{target};\nexport const extra = 1;\n",
        );
        let main_program = program(&session, MAIN_URI);

        let box_file = main_program
            .get_source_file(BOX_PATH)
            .expect("expected app.box to be loaded");
        assert!(
            box_file.text.contains("export const version = 7;"),
            "reparsed app.box was not transformed: {:?}",
            box_file.text
        );
        assert!(
            box_file.text.contains("export const extra = 1;"),
            "reparsed app.box missing the edit: {:?}",
            box_file.text
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:152 TestContentMapperInProject/watch change to a content-mapped file updates the program
    fn watch_change_to_a_content_mapped_file_updates_the_program() {
        let (session, utils) = in_project_session(true);

        open(&session, MAIN_URI, IN_PROJECT_MAIN);
        let original = program(&session, MAIN_URI)
            .get_source_file(BOX_PATH)
            .expect("expected app.box to be loaded");

        // Wait until the configured extension set has been published; watch filtering uses the set captured
        // when the snapshot change is created.
        session.wait_for_background_tasks();
        let updated_content = "export const version = #{target};\nexport const watched = true;\n";
        write_file(&utils, BOX_PATH, updated_content);
        watch(&session, &[(CHANGED, BOX_URI)]);

        let main_program = program(&session, MAIN_URI);
        let updated_snapshot = session.snapshot();
        let configured_project = updated_snapshot
            .get_default_project(&uri(MAIN_URI))
            .expect("expected configured project");
        assert_eq!(
            configured_project.borrow().program_update_kind,
            project::ProgramUpdateKind::CLONED
        );
        assert_eq!(
            configured_project.borrow().program_last_update,
            updated_snapshot.id()
        );
        let updated = main_program
            .get_source_file(BOX_PATH)
            .expect("expected app.box to remain loaded");
        assert!(
            !Rc::ptr_eq(&updated, &original),
            "expected the watched content-mapped file to be reparsed"
        );
        assert!(
            updated.text.contains("export const version = 7;"),
            "updated app.box was not transformed: {:?}",
            updated.text
        );
        assert!(
            updated.text.contains("export const watched = true;"),
            "updated app.box missing watched change: {:?}",
            updated.text
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:189 TestContentMapperInProject/unchanged content-mapped file is reused from the cache across a full rebuild
    fn unchanged_content_mapped_file_is_reused_from_the_cache_across_a_full_rebuild() {
        let (session, utils) = in_project_session(true);

        open(&session, MAIN_URI, IN_PROJECT_MAIN);
        let box_file = program(&session, MAIN_URI)
            .get_source_file(BOX_PATH)
            .expect("expected app.box to be loaded");
        assert!(
            box_file.text.contains("export const version = 7;"),
            "app.box was not transformed: {:?}",
            box_file.text
        );

        // Changing a compiler option the mapper does not depend on (strict) forces a full program
        // rebuild while leaving app.box's content and the mapper's transform identity unchanged, so the
        // transformed file must be served from the parse cache rather than re-transformed.
        write_file(
            &utils,
            "/home/project/tsconfig.json",
            r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": false },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
        );
        watch(&session, &[(CHANGED, "file:///home/project/tsconfig.json")]);

        let rebuilt_box = source_file(&program(&session, MAIN_URI), BOX_PATH);
        assert!(
            Rc::ptr_eq(&rebuilt_box, &box_file),
            "expected the unchanged content-mapped file to be reused from the parse cache, not re-transformed"
        );
        session.close();
    }
}

// ---------------------------------------------------------------------------
// Configured projects
// ---------------------------------------------------------------------------

child_test! {
    // Go: contentmapper_test.go:219 TestContentMapperPackageManifestChangeReloadsConfig
    fn content_mapper_package_manifest_change_reloads_config() {
        const PACKAGE_JSON_PATH: &str = "/home/mapper/package.json";
        const MAIN_TEXT: &str = "import { version } from \"./app.box\";\n";
        let mut file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler" },
			"contentMappers": [{ "package": "mapper", "extensions": [".box"] }]
		}"#,
            ),
            (
                PACKAGE_JSON_PATH,
                r#"{
			"name": "mapper",
			"version": "1.0.0",
			"typescript": { "contentMapper": { "exec": ["compiler-test-mapper"] } }
		}"#,
            ),
            ("/home/project/app.box", BOX_TEXT),
            ("/home/project/main.ts", MAIN_TEXT),
        ]);
        file_map.insert(
            "/home/project/node_modules/mapper".to_string(),
            vfstest::symlink("/home/mapper"),
        );
        let mut caps = lsproto::ResolvedClientCapabilities::default();
        caps.workspace.did_change_watched_files.relative_pattern_support = true;
        let ctx = lsproto::with_client_capabilities(&bg(), Arc::new(caps));
        let (mut init, utils) = init_options(
            file_map,
            SessionOptions {
                watch_enabled: true,
                ..options("/home/project", true)
            },
        );
        init.background_ctx = ctx.clone();
        init.spawner = Some(contentmappertest::new_spawner());
        let session = project::new_session(&init);

        let main_uri = uri(MAIN_URI);
        session.did_open_file(
            &ctx,
            &main_uri,
            1,
            MAIN_TEXT,
            &lsproto::LanguageKind::TYPE_SCRIPT,
        );
        if let Err(err) = session.get_language_service(&ctx, &main_uri) {
            panic!("GetLanguageService: {}", err.error());
        }
        let configured_project = session
            .snapshot()
            .get_default_project(&main_uri)
            .expect("expected a configured project");
        let mappers = configured_project
            .borrow()
            .command_line
            .as_ref()
            .expect("expected a command line")
            .content_mappers()
            .to_vec();
        assert_eq!(mappers.len(), 1);
        assert_eq!(mappers[0].package_directory, "/home/mapper");
        session.wait_for_background_tasks();
        assert!(
            utils.watches_file(PACKAGE_JSON_PATH),
            "expected the invalid mapper package manifest to be watched"
        );
        let has_external_watcher = utils.client().watch_files_calls().iter().any(|call| {
            call.watchers.iter().any(|watcher| {
                watcher
                    .glob_pattern
                    .relative_pattern
                    .as_ref()
                    .is_some_and(|relative| {
                        relative
                            .base_uri
                            .uri
                            .as_ref()
                            .is_some_and(|base_uri| base_uri.0 == "file:///home/mapper")
                            && relative.pattern == "**/*"
                    })
            })
        });
        assert!(
            has_external_watcher,
            "expected an external relative-pattern watcher for the mapper package"
        );

        let fixed_manifest = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER)
            .replacen(r#""version": "1.0.0""#, r#""version": "2.0.0""#, 1);
        assert!(fixed_manifest.contains(r#""version": "2.0.0""#));
        write_file(&utils, PACKAGE_JSON_PATH, &fixed_manifest);
        session.did_change_watched_files(
            &ctx,
            &[file_event(&format!("file://{PACKAGE_JSON_PATH}"), CHANGED)],
        );

        let language_service = session
            .get_language_service(&ctx, &main_uri)
            .unwrap_or_else(|err| panic!("GetLanguageService: {}", err.error()));
        let box_file = language_service
            .program
            .get_source_file(BOX_PATH)
            .expect("expected app.box in the rebuilt program");
        assert!(
            box_file.text.contains("export const version = 7;"),
            "expected fixed mapper manifest to be reloaded: {:?}",
            box_file.text
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:290 TestContentMapperSupplementalFileClonedOnEdit
    // PORT: Go `file.Hash` is `project::source_file_hash(file.text)`. The
    // old hashes are read before the edit: the parse cache forgets the hash
    // of a file when its last program lets it go (Go keeps it in the file).
    fn content_mapper_supplemental_file_cloned_on_edit() {
        const MAIN_TEXT: &str = "const value: number = supplementalValue;\n";
        let mapper = contentmappertest::package_json(contentmappertest::SUPPLEMENTAL_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{ "compilerOptions": { "strict": true }, "contentMappers": [{ "package": "mapper", "extensions": [".box"] }] }"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/app.box", "declare const supplementalValue: number;\n"),
            ("/home/project/extra.d.ts", "interface Extra {}\n"),
            ("/home/project/main.ts", MAIN_TEXT),
        ]);
        let (session, utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        open(&session, MAIN_URI, MAIN_TEXT);
        let old_program = program(&session, MAIN_URI);
        let old_canonical = source_file(&old_program, BOX_PATH);
        let old_supplemental = old_canonical.supplemental_source_files();
        assert_eq!(old_supplemental.len(), 1);
        assert_eq!(old_supplemental[0].file_name(), "/home/project/app.box.0.ts");
        assert_eq!(old_supplemental[0].path(), &path("/home/project/app.box.0.ts"));
        let old_supplemental_hash = project::source_file_hash(old_supplemental[0].text);
        assert_eq!(
            old_supplemental_hash,
            project::source_file_hash(old_canonical.text)
        );
        assert!(
            old_program
                .get_source_file_by_path(old_supplemental[0].path())
                .is_some_and(|file| Rc::ptr_eq(&file, &old_supplemental[0]))
        );
        assert!(
            old_program
                .files_by_path()
                .get(old_supplemental[0].path())
                .is_some_and(|file| Rc::ptr_eq(file, &old_supplemental[0]))
        );

        write_file(&utils, BOX_PATH, "declare const supplementalValue: string;\n");
        watch(&session, &[(CHANGED, BOX_URI)]);
        let new_program = program(&session, MAIN_URI);
        let configured_project = default_project(&session, MAIN_URI);
        assert_eq!(
            configured_project.borrow().program_update_kind,
            project::ProgramUpdateKind::CLONED
        );

        let new_canonical = source_file(&new_program, BOX_PATH);
        let new_supplemental = new_canonical.supplemental_source_files();
        assert_eq!(new_supplemental.len(), 1);
        assert_eq!(new_supplemental[0].path(), old_supplemental[0].path());
        assert!(!Rc::ptr_eq(&new_canonical, &old_canonical));
        assert!(!Rc::ptr_eq(&new_supplemental[0], &old_supplemental[0]));
        let new_supplemental_hash = project::source_file_hash(new_supplemental[0].text);
        assert_eq!(
            new_supplemental_hash,
            project::source_file_hash(new_canonical.text)
        );
        assert_ne!(new_supplemental_hash, old_supplemental_hash);
        assert!(
            new_program
                .files_by_path()
                .get(new_supplemental[0].path())
                .is_some_and(|file| Rc::ptr_eq(file, &new_supplemental[0]))
        );
        assert!(new_supplemental[0].text.contains("supplementalValue: string"));
        let main_file = source_file(&new_program, "/home/project/main.ts");
        let diagnostics = ls_program::get_semantic_diagnostics(
            &new_program,
            &projecttestutil::with_request_id(&bg()),
            main_file.root,
        );
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code() == 2322));

        // Changing the supplemental file's reference graph must fall back from cloning to a full rebuild.
        write_file(
            &utils,
            BOX_PATH,
            "/// <reference path=\"./extra.d.ts\" />\ndeclare const supplementalValue: string;\n",
        );
        watch(&session, &[(CHANGED, BOX_URI)]);
        program(&session, MAIN_URI);
        let configured_project = default_project(&session, MAIN_URI);
        assert_eq!(
            configured_project.borrow().program_update_kind,
            project::ProgramUpdateKind::SAME_FILE_NAMES
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:363 TestContentMapperModuleExtensionClonedOnUnrelatedEdit
    fn content_mapper_module_extension_cloned_on_unrelated_edit() {
        const MAIN_TEXT: &str = r#"import { value } from "./app.box"; value;"#;
        let mapper = contentmappertest::package_json(contentmappertest::MODULE_VERBATIM_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{ "contentMappers": [{ "package": "mapper", "extensions": [".box"] }] }"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/app.box", "export const value = 1;\n"),
            ("/home/project/main.ts", MAIN_TEXT),
        ]);
        let (session, _utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        open(&session, MAIN_URI, MAIN_TEXT);
        let mapped_file = source_file(&program(&session, MAIN_URI), BOX_PATH);
        assert_eq!(mapped_file.virtual_file_name(), "/home/project/app.box.mts");
        assert!(mapped_file.parse_options().external_module_indicator_options.force);

        change_whole(
            &session,
            MAIN_URI,
            2,
            r#"import { value } from "./app.box"; value + 1;"#,
        );
        let main_program = program(&session, MAIN_URI);
        let configured_project = default_project(&session, MAIN_URI);
        assert_eq!(
            configured_project.borrow().program_update_kind,
            project::ProgramUpdateKind::CLONED
        );
        assert!(
            main_program
                .get_source_file(BOX_PATH)
                .is_some_and(|file| Rc::ptr_eq(&file, &mapped_file))
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:402 TestContentMapperLocaleChange
    // PORT: Go guards `currentLocale` with a mutex; the client mock runs on
    // this thread, so it is a `RefCell`.
    fn content_mapper_locale_change() {
        const MAIN_TEXT: &str = r#"import { value } from "./app.box"; value;"#;
        let mapper = contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{ "contentMappers": [ { "package": "mapper", "extensions": [".box"] } ] }"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/app.box", "export const value = 1;\n"),
            ("/home/project/main.ts", MAIN_TEXT),
        ]);
        let (mut init, utils) = init_options(file_map, options("/home/project", true));
        let spawner = RecordingContentMapperSpawner::new(contentmappertest::new_spawner());
        let spawner_for_init: Rc<dyn contentmapper::Spawner> = spawner.clone();
        init.spawner = Some(spawner_for_init);

        let current_locale = Rc::new(RefCell::new(locale::DEFAULT));
        {
            let current_locale = current_locale.clone();
            *utils.client().get_locale_func.borrow_mut() =
                Some(Box::new(move || current_locale.borrow().clone()));
        }
        *utils.client().set_locale_func.borrow_mut() = Some(Box::new(move |value: &str| {
            let (updated, ok) = locale::parse(value);
            assert!(ok);
            *current_locale.borrow_mut() = updated;
        }));

        let session = project::new_session(&init);
        // ts#64163
        let ctx = locale::with_locale(&bg(), locale::DEFAULT);
        let locale_reads = utils.client().get_locale_calls();
        session.did_open_file(&ctx, &uri(MAIN_URI), 1, MAIN_TEXT, &lsproto::LanguageKind::TYPE_SCRIPT);
        session
            .get_language_service(&ctx, &uri(MAIN_URI))
            .unwrap_or_else(|err| panic!("GetLanguageService: {}", err.error()));
        // Snapshot adoption reads the current locale for its background work; project construction should not.
        assert_eq!(utils.client().get_locale_calls(), locale_reads + 1);
        assert_eq!(spawner.spawns(), 1);

        let mut preferences = session.config();
        preferences.locale = "fr".to_string();
        session.configure(preferences);
        assert_eq!(spawner.closes(), 1);

        program(&session, MAIN_URI);
        assert_eq!(spawner.spawns(), 2);
        session.close();
    }
}

// ---------------------------------------------------------------------------
// Dynamic mappers
// ---------------------------------------------------------------------------

const DYNAMIC_MAIN: &str = r#"import { value } from "./app.box"; value;"#;

child_test! {
    // Go: contentmapper_test.go:452 TestDynamicContentMapperInProject
    fn dynamic_content_mapper_in_project() {
        let mapper = contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{ "contentMappers": [ { "package": "mapper", "extensions": [".box"], "options": { "mode": "project" } } ] }"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/mapper.config.json", r#"{ "version": 1 }"#),
            ("/home/project/app.box", "export const value = 1;\n"),
            ("/home/project/main.ts", DYNAMIC_MAIN),
        ]);
        let (session, utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        open(&session, MAIN_URI, DYNAMIC_MAIN);
        let first_program = program(&session, MAIN_URI);
        let mapped_file = source_file(&first_program, BOX_PATH);
        assert!(!mapped_file.is_content_mapper_failure_stub());

        write_file(&utils, "/home/project/mapper.config.json", r#"{ "version": 2 }"#);
        watch(&session, &[(CHANGED, "file:///home/project/mapper.config.json")]);
        let second_program = program(&session, MAIN_URI);
        assert!(!Rc::ptr_eq(&second_program, &first_program));
        let mapped_file = source_file(&second_program, BOX_PATH);
        assert!(!mapped_file.is_content_mapper_failure_stub());
        session.close();
    }
}

// Go: contentmapper_test.go:531 TestDynamicContentMapperRefreshesForMixedWatchBatches (the body of each subtest)
fn refreshes_for_mixed_watch_batch(events: &[lsproto::FileEvent]) {
    let mapper = contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER);
    let file_map = files(&[
        (
            "/home/project/tsconfig.json",
            r#"{ "contentMappers": [{ "package": "mapper", "extensions": [".box"] }] }"#,
        ),
        (
            "/home/project/node_modules/mapper/package.json",
            mapper.as_str(),
        ),
        ("/home/project/mapper.config.json", r#"{ "version": 1 }"#),
        ("/home/project/app.box", "export const value = 1;\n"),
        ("/home/project/main.ts", DYNAMIC_MAIN),
    ]);
    let (mut init, _utils) = init_options(file_map, options("/home/project", true));
    let lifecycle = Arc::new(contentmappertest::ProjectLifecycle::default());
    init.spawner = Some(contentmappertest::new_spawner_with_project_lifecycle(
        lifecycle.clone(),
    ));
    let session = project::new_session(&init);

    open(&session, MAIN_URI, DYNAMIC_MAIN);
    program(&session, MAIN_URI);
    assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 1);
    assert_eq!(lifecycle.closes.load(Ordering::SeqCst), 0);

    session.did_change_watched_files(&bg(), events);
    session.wait_for_background_tasks();
    program(&session, MAIN_URI);
    assert_eq!(lifecycle.closes.load(Ordering::SeqCst), 1);
    assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 2);
    session.close();
}

child_test! {
    // Go: contentmapper_test.go:500 TestDynamicContentMapperRefreshesForMixedWatchBatches/excessive events
    fn excessive_events() {
        let mut events: Vec<lsproto::FileEvent> = (0..1001)
            .map(|i| file_event(&format!("file:///home/project/noise-{i}.ts"), CHANGED))
            .collect();
        events[0] = file_event("file:///home/project/mapper.config.json", CHANGED);
        events[1] = file_event(MAIN_URI, CHANGED);
        refreshes_for_mixed_watch_batch(&events);
    }
}

child_test! {
    // Go: contentmapper_test.go:512 TestDynamicContentMapperRefreshesForMixedWatchBatches/changed files make project fully dirty before mapper deletion
    fn changed_files_make_project_fully_dirty_before_mapper_deletion() {
        refreshes_for_mixed_watch_batch(&[
            file_event(MAIN_URI, CHANGED),
            file_event(BOX_URI, CHANGED),
            file_event("file:///home/project/mapper.config.json", DELETED),
        ]);
    }
}

child_test! {
    // Go: contentmapper_test.go:522 TestDynamicContentMapperRefreshesForMixedWatchBatches/changed files make project fully dirty before mapper creation
    fn changed_files_make_project_fully_dirty_before_mapper_creation() {
        refreshes_for_mixed_watch_batch(&[
            file_event(MAIN_URI, CHANGED),
            file_event(BOX_URI, CHANGED),
            file_event("file:///home/project/mapper.config.json", CREATED),
        ]);
    }
}

child_test! {
    // Go: contentmapper_test.go:571 TestUnusedDynamicContentMapperIsNotOpened
    fn unused_dynamic_content_mapper_is_not_opened() {
        const MAIN_TEXT: &str = "export const value = 1;";
        let mapper = contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{ "contentMappers": [{ "package": "mapper", "extensions": [".box"] }] }"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/main.ts", MAIN_TEXT),
        ]);
        let (mut init, _utils) = init_options(file_map, options("/home/project", true));
        let lifecycle = Arc::new(contentmappertest::ProjectLifecycle::default());
        init.spawner = Some(contentmappertest::new_spawner_with_project_lifecycle(
            lifecycle.clone(),
        ));
        let session = project::new_session(&init);

        open(&session, MAIN_URI, MAIN_TEXT);
        program(&session, MAIN_URI);
        assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 0);
        session.close();
    }
}

// ---------------------------------------------------------------------------
// Several projects and inferred projects
// ---------------------------------------------------------------------------

child_test! {
    // Go: contentmapper_test.go:597 TestContentMappersInParallelProjectReferences
    fn content_mappers_in_parallel_project_references() {
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"files": ["src/index.d.ts"],
			"references": [{ "path": "./a" }, { "path": "./b" }]
		}"#,
            ),
            ("/home/project/src/index.d.ts", "export {};"),
            (
                "/home/project/a/tsconfig.json",
                r#"{
			"compilerOptions": { "composite": true },
			"files": ["../src/index.d.ts"],
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#,
            ),
            (
                "/home/project/b/tsconfig.json",
                r#"{
			"compilerOptions": { "composite": true },
			"files": ["../src/index.d.ts"],
			"contentMappers": [{ "package": "mapper", "extensions": [".svelte"] }]
		}"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
        ]);
        let (session, utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        open(&session, "file:///home/project/src/index.d.ts", "export {};");
        session.wait_for_background_tasks();
        let calls = utils.client().register_content_mapper_extensions_calls();
        let mut extensions = calls
            .last()
            .expect("expected RegisterContentMapperExtensions to be called")
            .clone();
        extensions.sort();
        assert_eq!(extensions, vec![".svelte".to_string(), ".vue".to_string()]);
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:638 TestContentMapperOpenFileExcludedByConfigChange
    fn content_mapper_open_file_excluded_by_config_change() {
        const SRC_BOX_URI: &str = "file:///home/project/src/app.box";
        const SRC_BOX_PATH: &str = "/home/project/src/app.box";
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": true },
			"include": ["src"],
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            (SRC_BOX_PATH, BOX_TEXT),
            ("/home/project/src/main.ts", "export const main = true;\n"),
        ]);
        let (session, utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        session.set_content_mapper_contributions(
            &bg(),
            box_contributions("/home/project"),
            Vec::new(),
        );
        open_kind(&session, SRC_BOX_URI, BOX_TEXT, box_kind());
        assert!(program(&session, SRC_BOX_URI).get_source_file(SRC_BOX_PATH).is_some());

        write_file(
            &utils,
            "/home/project/tsconfig.json",
            r#"{
		"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": true },
		"include": ["src/**/*.ts"],
		"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
	}"#,
        );
        watch(&session, &[(CHANGED, "file:///home/project/tsconfig.json")]);

        let box_program = program(&session, SRC_BOX_URI);
        let default_project = default_project(&session, SRC_BOX_URI);
        assert_eq!(default_project.borrow().kind, project::Kind::INFERRED);
        let box_file = box_program
            .get_source_file(SRC_BOX_PATH)
            .expect("expected the open app.box in the inferred project");
        assert!(
            !box_file.content_mapper().is_empty(),
            "expected app.box to retain its content mapper"
        );
        assert!(
            !box_file.text.contains("#{target}"),
            "expected app.box to be transformed: {:?}",
            box_file.text
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:698 TestContentMapperRemovalWithOpenFile
    fn content_mapper_removal_with_open_file() {
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler" },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            (BOX_PATH, BOX_TEXT),
        ]);
        let spawner = RecordingContentMapperSpawner::new(contentmappertest::new_spawner());
        let (session, utils) =
            new_session(file_map, options("/home/project", true), spawner.clone());

        open_kind(&session, BOX_URI, BOX_TEXT, box_kind());
        assert!(
            !source_file(&program(&session, BOX_URI), BOX_PATH)
                .content_mapper()
                .is_empty()
        );
        assert_eq!(spawner.spawns(), 1);
        assert_eq!(spawner.closes(), 0);
        for version in 2..=4 {
            change_whole(
                &session,
                BOX_URI,
                version,
                &format!("export const version = {version};\n"),
            );
            program(&session, BOX_URI);
            assert_eq!(spawner.spawns(), 1, "snapshot clone should reuse the mapper process");
            assert_eq!(
                spawner.closes(),
                0,
                "snapshot clone should preserve overlapping ownership"
            );
        }
        let release_old_snapshot = session
            .with_language_service_and_snapshot(&bg(), &uri(BOX_URI), |_language_service, _snapshot| {
                let release: Box<dyn FnOnce() -> Result<(), GoError>> = Box::new(|| Ok(()));
                Ok(Some(release))
            })
            .unwrap_or_else(|err| panic!("WithLanguageServiceAndSnapshot: {}", err.error()))
            .expect("expected the release function");

        write_file(
            &utils,
            "/home/project/tsconfig.json",
            r#"{
		"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler" }
	}"#,
        );
        watch(&session, &[(CHANGED, "file:///home/project/tsconfig.json")]);

        assert_no_project(&session, BOX_URI);
        assert!(
            session.snapshot().get_file(BOX_PATH).is_some(),
            "overlay should remain until didClose"
        );
        assert!(
            session.snapshot().get_default_project(&uri(BOX_URI)).is_none(),
            "unsupported file should not be in a project"
        );

        session.wait_for_background_tasks();
        assert_eq!(
            spawner.closes(),
            0,
            "live old snapshot should retain the mapper process"
        );
        if let Err(err) = release_old_snapshot() {
            panic!("release: {}", err.error());
        }
        assert_eq!(
            spawner.closes(),
            1,
            "process should close after the final live snapshot is released"
        );
        let calls = utils.client().register_content_mapper_extensions_calls();
        let last = calls
            .last()
            .expect("expected content mapper registration updates");
        assert!(
            last.is_empty(),
            "expected content mapper extensions to be unregistered"
        );

        close(&session, BOX_URI);
        assert_no_project(&session, BOX_URI);
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:768 TestContentMapperProcessSharedAcrossProjects
    fn content_mapper_process_shared_across_projects() {
        const A_URI: &str = "file:///home/a/app.box";
        const B_URI: &str = "file:///home/b/app.panel";
        let config = |extension: &str| {
            format!(
                r#"{{
			"compilerOptions": {{ "target": "es2020", "module": "esnext", "moduleResolution": "bundler" }},
			"contentMappers": [ {{ "package": "mapper", "extensions": [{}] }} ]
		}}"#,
                strconv::quote(extension)
            )
        };
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let a_config = config(".box");
        let b_config = config(".panel");
        let file_map = files(&[
            ("/home/a/tsconfig.json", a_config.as_str()),
            ("/home/a/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/a/app.box", "export const a = 1;\n"),
            ("/home/b/tsconfig.json", b_config.as_str()),
            ("/home/b/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/b/app.panel", "export const b = 1;\n"),
        ]);
        let spawner = RecordingContentMapperSpawner::new(contentmappertest::new_spawner());
        let (session, utils) = new_session(file_map, options("/home", true), spawner.clone());

        open_kind(&session, A_URI, "export const a = 1;\n", box_kind());
        program(&session, A_URI);
        open_kind(
            &session,
            B_URI,
            "export const b = 1;\n",
            lsproto::LanguageKind("panel".into()),
        );
        program(&session, B_URI);
        assert_eq!(spawner.spawns(), 1, "same mapper identity should share one process");

        write_file(&utils, "/home/a/tsconfig.json", "{}");
        watch(&session, &[(CHANGED, "file:///home/a/tsconfig.json")]);
        assert_no_project(&session, A_URI);
        assert_eq!(spawner.closes(), 0, "second project still owns the shared process");

        write_file(&utils, "/home/b/tsconfig.json", "{}");
        watch(&session, &[(CHANGED, "file:///home/b/tsconfig.json")]);
        assert_no_project(&session, B_URI);
        assert_eq!(spawner.closes(), 1, "final project owner should close the shared process");
        session.close();
    }
}

const CONFIGURED_URI: &str = "file:///home/configured/main.ts";
const CONFIGURED_MAIN: &str = "export const main = true;\n";
const LOOSE_BOX_URI: &str = "file:///home/loose/app.box";
const LOOSE_BOX_PATH: &str = "/home/loose/app.box";

// Go: contentmapper_test.go:822 and :879, the configured project and the loose app.box
fn loose_box_files(mapper: &str) -> FileMap {
    files(&[
        (
            "/home/configured/tsconfig.json",
            r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler" },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
        ),
        ("/home/configured/node_modules/mapper/package.json", mapper),
        ("/home/configured/main.ts", CONFIGURED_MAIN),
        (LOOSE_BOX_PATH, BOX_TEXT),
    ])
}

child_test! {
    // Go: contentmapper_test.go:820 TestContentMapperInferredProjectUsesExtensionContributions
    fn content_mapper_inferred_project_uses_extension_contributions() {
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let (session, _utils) = new_session(
            loose_box_files(&mapper),
            options("/home", true),
            contentmappertest::new_spawner(),
        );

        open(&session, CONFIGURED_URI, CONFIGURED_MAIN);
        program(&session, CONFIGURED_URI);

        open_kind(&session, LOOSE_BOX_URI, BOX_TEXT, box_kind());
        // The configured mapper must not leak into inferred projects.
        assert_no_project(&session, LOOSE_BOX_URI);
        session.set_content_mapper_contributions(
            &bg(),
            box_contributions("/home"),
            vec![uri(LOOSE_BOX_URI)],
        );
        let box_program = program(&session, LOOSE_BOX_URI);
        let default_project = default_project(&session, LOOSE_BOX_URI);
        assert_eq!(default_project.borrow().kind, project::Kind::INFERRED);
        let box_file = box_program
            .get_source_file(LOOSE_BOX_PATH)
            .expect("expected loose app.box in the inferred project");
        assert!(
            !box_file.content_mapper().is_empty(),
            "expected loose app.box to use the extension contribution"
        );
        assert!(
            !box_file.text.contains("#{target}"),
            "expected loose app.box to be transformed: {:?}",
            box_file.text
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:872 TestContentMapperInferredProjectSurvivesTypingsInstall
    fn content_mapper_inferred_project_survives_typings_install() {
        // A loose content-mapped file lands in the inferred project with an extension content mapper.
        // When ATA finishes installing typings, the inferred program rebuilds with the
        // typings-augmented command line; if that command line drops the content mappers, the
        // otherwise unsupported root file is parsed as plain TypeScript with an unknown script kind and the
        // server panics.
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let mut file_map = loose_box_files(&mapper);
        file_map.insert(
            "/home/package.json".to_string(),
            r#"{"name":"loose","dependencies":{"jquery":"^3.1.0"}}"#.into(),
        );
        let (mut init, utils) = projecttestutil::get_session_init_options(
            file_map,
            Some(SessionOptions {
                logging_enabled: true,
                ..options("/home", true)
            }),
            TypingsInstallerOptions {
                package_to_file: [(
                    "jquery".to_string(),
                    "declare const $: { x: number }".to_string(),
                )]
                .into_iter()
                .collect(),
                ..Default::default()
            },
        );
        init.spawner = Some(contentmappertest::new_spawner());
        let session = project::new_session(&init);

        session.set_content_mapper_contributions(&bg(), box_contributions("/home"), Vec::new());
        open(&session, CONFIGURED_URI, CONFIGURED_MAIN);
        program(&session, CONFIGURED_URI);

        open_kind(&session, LOOSE_BOX_URI, BOX_TEXT, box_kind());
        program(&session, LOOSE_BOX_URI);
        let default_project = default_project(&session, LOOSE_BOX_URI);
        assert_eq!(default_project.borrow().kind, project::Kind::INFERRED);

        // Let ATA install the typings in the background.
        session.wait_for_background_tasks();
        assert!(
            !utils.npm_executor().npm_install_calls().is_empty(),
            "expected ATA to install typings"
        );

        // Applying the typings change rebuilds the inferred program with the typings-augmented
        // command line. The content mappers must survive that rebuild.
        let box_program = program(&session, LOOSE_BOX_URI);
        let box_file = box_program
            .get_source_file(LOOSE_BOX_PATH)
            .expect("expected loose app.box in the inferred project after typings install");
        assert!(
            !box_file.content_mapper().is_empty(),
            "expected loose app.box to keep its content mapper after typings install"
        );
        assert!(
            !box_file.text.contains("#{target}"),
            "expected loose app.box to be transformed after typings install: {:?}",
            box_file.text
        );
        assert!(
            box_program
                .source_files()
                .iter()
                .any(|file| file.file_name().ends_with("@types/jquery/index.d.ts")),
            "expected installed typings in the inferred program (the typings-augmented rebuild did not happen)"
        );
        session.close();
    }
}

child_test! {
    // Go: contentmapper_test.go:948 TestContentMapperCreatedFileAdoptedByConfiguredProject
    fn content_mapper_created_file_adopted_by_configured_project() {
        // A content-mapped file created while the server is running must be adopted by the
        // configured project: the created-file root matching has to account for the content
        // mapper extensions, otherwise the file falls into the inferred project until a full
        // project reload.
        const NEW_BOX_URI: &str = "file:///home/project/new.box";
        const NEW_BOX_PATH: &str = "/home/project/new.box";
        let mapper = contentmappertest::package_json(contentmappertest::TRANSFORMING_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler" },
			"contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
		}"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/main.ts", CONFIGURED_MAIN),
        ]);
        let (session, utils) = new_session(
            file_map,
            options("/home/project", true),
            contentmappertest::new_spawner(),
        );

        open(&session, MAIN_URI, CONFIGURED_MAIN);
        program(&session, MAIN_URI);

        write_file(&utils, NEW_BOX_PATH, BOX_TEXT);
        watch(&session, &[(CREATED, NEW_BOX_URI)]);
        open_kind(&session, NEW_BOX_URI, BOX_TEXT, box_kind());
        let box_program = program(&session, NEW_BOX_URI);
        let default_project = default_project(&session, NEW_BOX_URI);
        assert_eq!(default_project.borrow().kind, project::Kind::CONFIGURED);
        let box_file = box_program
            .get_source_file(NEW_BOX_PATH)
            .expect("expected new.box in the configured project");
        assert!(
            !box_file.text.contains("#{target}"),
            "expected new.box to be transformed: {:?}",
            box_file.text
        );
        session.close();
    }
}
