//! PORT: no Go counterpart (editfuzz4 G2, lane csfree1). Go
//! `encodeLeasedSourceFile` (api/session.go:1876) encodes the leased
//! `*ast.SourceFile`, and the encoder reads its `Hash` and `ParseOptions()`
//! (api/encoder/encoder.go:595-596). The port keeps both in the
//! `ParsedSourceFile` that the lease holds, and the encoder reads them there.
//! These tests cover the leases that a lookup by the root node does not find:
//! - a freeable parse outside a program: in a language server process a new
//!   parse of a path that the server published is a freeable file version
//!   (`ast::freeable_path`, lsshells M3a);
//! - a parse that a program loaded, after that program is released, while
//!   an earlier lease keeps it in the parse cache (the skeptic's
//!   sk-min-stdio-static and sk-min-lsp-snaprel shapes).
//!
//! The expected header is Go's: the hash is `fh.Hash()`, the xxh3-128 of the
//! text (project/parsecache.go:79), and the parse options of a lease have a
//! zero `ExternalModuleIndicatorOptions` (api/session.go:1866-1869).
//!
//! Lane apimem1: Go's GC frees a leased `*ast.SourceFile` when its last
//! lease is released and no program or cache entry has it
//! (api/session.go:1893 `handleReleaseSourceFile`). The tests at the end
//! check that the port frees the version at that release, with no program
//! release, also in the plain API (`api::new_standalone_session`) and for a
//! path that no program has (`project::drop_released_lease`).

use std::rc::Rc;

use ts_goport::api::{
    self, CreateSourceFileFromFileParams, CreateSourceFileOptions, RawBinary,
    ReleaseSourceFileParams, SourceFileLeaseID, SourceFileResponse,
};
use ts_goport::ast::{
    FileVersionProbe, file_version_probe, free_file_versions, release_file_version_pins,
};
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::json_ext::AnyValue;
use ts_goport::frontend::parser::ParsedSourceFile;
use ts_goport::gostd;
use ts_goport::program::ls_program;
use ts_goport::project::{self, SourceFileLease};

use super::api_util::nil_error;
use super::projecttestutil::{self, TypingsInstallerOptions, files};
use super::util::{bg, edit, open, program, sem_diag_count};

const INDEX_URI: &str = "file:///home/projects/TS/p1/index.ts";
const INDEX_FILE: &str = "/home/projects/TS/p1/index.ts";
const INDEX_TEXT: &str = "import { a } from './a';\nexport const x = a + 1;";
const A_URI: &str = "file:///home/projects/TS/p1/a.ts";
const A_FILE: &str = "/home/projects/TS/p1/a.ts";
const A_TEXT: &str = "export const a = 1;";

/// A project session with index.ts open and its program loaded, so the
/// server published index.ts and a.ts, and its API session.
fn setup() -> (Rc<project::Session>, Rc<api::Session>) {
    let (project_session, _) = projecttestutil::setup(files(&[
        ("/home/projects/TS/p1/tsconfig.json", "{}"),
        (INDEX_FILE, INDEX_TEXT),
        (A_FILE, A_TEXT),
    ]));
    open(&project_session, INDEX_URI, INDEX_TEXT);
    let _ = program(&project_session, INDEX_URI);
    // The queued diagnostics task of a snapshot change reads the programs of
    // its new snapshot. It runs before the next change releases them.
    project_session.wait_for_background_tasks();
    assert!(
        free_file_versions(),
        "a session process frees file versions"
    );
    let session = api::new_lsp_session(project_session.clone(), None);
    (project_session, session)
}

/// The bytes of an encoded source file answer.
fn encoded_bytes(answer: Option<Box<dyn AnyValue>>) -> Vec<u8> {
    let answer = answer.expect("an encoded source file");
    if let Some(RawBinary(data)) = answer.downcast_ref::<RawBinary>() {
        return data.clone();
    }
    let response = answer
        .downcast_ref::<SourceFileResponse>()
        .expect("a SourceFileResponse");
    nil_error(api::base64_std_encoding_decode_string(&response.data))
}

/// The lease id in the header (bytes 52-59, Go `SetSourceFileLease`).
fn lease_id(data: &[u8]) -> SourceFileLeaseID {
    SourceFileLeaseID(u64::from_le_bytes(data[52..60].try_into().unwrap()))
}

/// Checks the header as Go writes it for a lease of `text`: bytes 4-11 are
/// `Hash.Lo` and bytes 12-19 `Hash.Hi` (u64 little-endian, Go
/// encoder.go:629-630), and bytes 20-23 the parse option bits (:631).
fn assert_header(data: &[u8], text: &str) {
    let hash = xxhash_rust::xxh3::xxh3_128(text.as_bytes());
    assert_eq!(data[4..12], (hash as u64).to_le_bytes(), "Hash.Lo");
    assert_eq!(data[12..20], ((hash >> 64) as u64).to_le_bytes(), "Hash.Hi");
    assert_eq!(data[20..24], [0; 4], "the parse option bits");
}

/// Encodes `lease` as `handleCreateSourceFile` does. Returns the bytes,
/// after a check of the header against `text`.
fn encode(session: &api::Session, lease: Rc<SourceFileLease>, text: &str) -> Vec<u8> {
    let data = encoded_bytes(nil_error(session.encode_leased_source_file(lease)));
    assert_header(&data, text);
    data
}

/// Releases the lease of the encoded `data`, as `releaseSourceFile` does.
fn release(session: &api::Session, data: &[u8]) {
    nil_error(
        session.handle_release_source_file(Some(&ReleaseSourceFileParams {
            lease: lease_id(data),
        })),
    );
}

/// Go `createSourceFile` of `file_name` with `text` and the default options.
fn lease(session: &api::Session, file_name: &str, text: &str) -> Rc<SourceFileLease> {
    nil_error(session.create_source_file(file_name, text, &CreateSourceFileOptions::default()))
}

/// The parse of `file_name` in the current program of the open file `u`.
fn program_parse(
    project_session: &Rc<project::Session>,
    u: &str,
    file_name: &str,
) -> Rc<ParsedSourceFile> {
    let program = program(project_session, u);
    project_session.wait_for_background_tasks();
    program
        .get_source_file(file_name)
        .unwrap_or_else(|| panic!("no source file {file_name}"))
}

/// Encodes a new parse of `file_name` with `text` through a lease, as
/// `handleCreateSourceFile` does, and releases the lease. The parse is a
/// freeable version, and only the lease holds it, so the release frees it:
/// the encoder's reads pinned it on this thread, and the release drops the
/// pins (`project::drop_released_lease`). This test thread does not keep
/// garbage (`gostd::local::keep_garbage`), so that runs at once.
fn encode_and_release(session: &api::Session, file_name: &str, text: &str) {
    let lease = lease(session, file_name, text);
    let version = file_version_probe(lease.source_file())
        .expect("a new parse of a published path is freeable");
    let data = encode(session, lease, text);
    release(session, &data);
    assert!(version.is_freed(), "the release frees the version");
}

/// Encodes `first`, a lease of `text` at a.ts that shares the parse of a
/// live program. Then `release_program` releases that program, and a second
/// lease of `text` gets the same parse, which only `first` keeps in the
/// parse cache. In Go both encodes come from one `*ast.SourceFile`, so they
/// are equal except for the lease id (bytes 52-59). Returns both encodes.
fn encode_before_and_after_program_release(
    project_session: &Rc<project::Session>,
    session: &api::Session,
    first: Rc<SourceFileLease>,
    text: &str,
    release_program: impl FnOnce(),
) -> (Vec<u8>, Vec<u8>) {
    let root = first.source_file();
    assert!(
        ls_program::program_parsed_source_file(root).is_some(),
        "the lease shares the program's parse"
    );
    let before = encode(session, first, text);

    release_program();
    project_session.wait_for_background_tasks();
    assert!(
        ls_program::program_parsed_source_file(root).is_none(),
        "no live program has the parse"
    );

    let second = lease(session, A_FILE, text);
    assert_eq!(
        second.source_file(),
        root,
        "the parse cache gives the leased parse"
    );
    let after = encode(session, second, text);
    assert_ne!(lease_id(&before), lease_id(&after));
    assert_eq!(before[..52], after[..52]);
    assert_eq!(before[60..], after[60..]);
    (before, after)
}

child_test! {
    // g2-cs-lsp-proj: a project file that is not open, with new text.
    fn project_file_with_new_text() {
        let (project_session, session) = setup();
        encode_and_release(&session, A_FILE, "export const a = 1;\nexport const b = 2;\n");
        session.close();
        project_session.close();
    }
}

child_test! {
    // g2-cs-lsp-open: the open file with new text.
    fn open_file_with_new_text() {
        let (project_session, session) = setup();
        encode_and_release(&session, INDEX_FILE, "export const x = 2;\n");
        session.close();
        project_session.close();
    }
}

child_test! {
    // r-csf-a: createSourceFileFromFile of a project file with another
    // script kind (JSX), so the parse cache key differs.
    fn project_file_from_file_with_another_script_kind() {
        let (project_session, session) = setup();
        let answer = nil_error(session.handle_create_source_file_from_file(
            &bg(),
            &CreateSourceFileFromFileParams {
                file_name: A_FILE.to_string(),
                options: CreateSourceFileOptions {
                    script_kind: ScriptKind::JSX,
                },
            },
        ));
        let data = encoded_bytes(answer);
        assert_header(&data, A_TEXT);
        release(&session, &data);
        session.close();
        project_session.close();
    }
}

child_test! {
    // sk-min-stdio-static: a lease of the disk text shares the static parse
    // of the first program. An edit of a.ts makes the next program, and the
    // first one is released. A second lease of the disk text gets the parse
    // that the first lease keeps in the parse cache.
    fn static_program_parse_after_the_program_release() {
        let (project_session, session) = setup();
        let first = lease(&session, A_FILE, A_TEXT);
        assert_eq!(first.source_file(), program_parse(&project_session, INDEX_URI, A_FILE).root);
        assert!(file_version_probe(first.source_file()).is_none(), "the first parse is static");

        let (before, after) =
            encode_before_and_after_program_release(&project_session, &session, first, A_TEXT, || {
                open(&project_session, A_URI, "export const a = 2;");
                let _ = program_parse(&project_session, INDEX_URI, A_FILE);
            });
        release(&session, &before);
        release(&session, &after);
        session.close();
        project_session.close();
    }
}

/// sk-min-lsp-snaprel: a program loads a freeable parse F' of a.ts, a lease
/// shares F', and the next edit releases that program. A second lease gets
/// F' again, which only the first lease keeps alive. The two leases are
/// released in the given order. The version lives while a lease holds it.
fn freeable_program_parse_after_the_program_release(first_released_first: bool) {
    const TEXT: &str = "export const a = 2;";
    let (project_session, session) = setup();
    open(&project_session, A_URI, TEXT);
    let loaded = program_parse(&project_session, A_URI, A_FILE).root;
    let first = lease(&session, A_FILE, TEXT);
    assert_eq!(first.source_file(), loaded);
    let version: FileVersionProbe = file_version_probe(first.source_file())
        .expect("a new parse of a published path is freeable");

    let (before, after) =
        encode_before_and_after_program_release(&project_session, &session, first, TEXT, || {
            edit(&project_session, A_URI, 2, (0, 17), (0, 18), "3");
            let parse = program_parse(&project_session, A_URI, A_FILE);
            assert_eq!(parse.text(), "export const a = 3;");
        });
    release_file_version_pins();
    assert!(!version.is_freed(), "the leases keep the version");

    let (released_first, released_last) = if first_released_first {
        (&before, &after)
    } else {
        (&after, &before)
    };
    release(&session, released_first);
    release_file_version_pins();
    assert!(!version.is_freed(), "the other lease keeps the version");
    release(&session, released_last);
    release_file_version_pins();
    assert!(version.is_freed(), "no lease keeps the version");
    session.close();
    project_session.close();
}

child_test! {
    fn freeable_program_parse_after_the_program_release_first_lease_first() {
        freeable_program_parse_after_the_program_release(true);
    }
}

child_test! {
    fn freeable_program_parse_after_the_program_release_second_lease_first() {
        freeable_program_parse_after_the_program_release(false);
    }
}

child_test! {
    // apimem1 problem 1 (sbml-loop): leases of new texts of a.ts, each
    // released before the next, with no program release in between. Each
    // release frees its version.
    fn released_leases_are_freed_with_no_program_release() {
        let (project_session, session) = setup();
        for n in 2..5 {
            encode_and_release(&session, A_FILE, &format!("export const a = {n};\n"));
        }
        session.close();
        project_session.close();
    }
}

child_test! {
    // On a thread that keeps its garbage (the LSP dispatch loop, the stdio
    // API server), the pin release of a lease release waits until
    // `drop_garbage`, after the answer.
    fn released_lease_is_freed_after_the_answer() {
        const TEXT: &str = "export const a = 2;\n";
        let (project_session, session) = setup();
        gostd::local::keep_garbage();
        let lease = lease(&session, A_FILE, TEXT);
        let version = file_version_probe(lease.source_file())
            .expect("a new parse of a published path is freeable");
        let data = encode(&session, lease, TEXT);
        release(&session, &data);
        assert!(!version.is_freed(), "the free waits for the answer");
        assert_eq!(gostd::local::garbage_len(), 1, "one pin release waits");
        gostd::local::drop_garbage(|| false);
        assert!(version.is_freed(), "the release frees the version after the answer");
        session.close();
        project_session.close();
    }
}

child_test! {
    // A lease that shares the freeable parse of a live program: its release
    // frees nothing, and the program reads the parse after it.
    fn lease_of_a_live_program_parse_is_kept_by_the_program() {
        const TEXT: &str = "export const a = 2;";
        let (project_session, session) = setup();
        open(&project_session, A_URI, TEXT);
        let root = program_parse(&project_session, A_URI, A_FILE).root;
        let version = file_version_probe(root).expect("a new parse of a published path is freeable");
        let lease = lease(&session, A_FILE, TEXT);
        assert_eq!(lease.source_file(), root, "the lease shares the program's parse");
        let data = encode(&session, lease, TEXT);
        release(&session, &data);
        assert!(!version.is_freed(), "the program keeps the version");
        let program = program(&project_session, A_URI);
        assert_eq!(program.get_source_file(A_FILE).map(|parsed| parsed.root), Some(root));
        assert_eq!(sem_diag_count(&program, A_FILE), 0, "the checker reads the parse");
        session.close();
        project_session.close();
    }
}

/// Two leases of one freeable parse, released in the given order: the
/// version lives until the second release.
fn two_leases_of_one_parse(first_released_first: bool) {
    const TEXT: &str = "export const a = 5;\n";
    let (project_session, session) = setup();
    let first = lease(&session, A_FILE, TEXT);
    let second = lease(&session, A_FILE, TEXT);
    assert_eq!(
        first.source_file(),
        second.source_file(),
        "the parse cache gives one parse"
    );
    let version = file_version_probe(first.source_file())
        .expect("a new parse of a published path is freeable");
    let first = encode(&session, first, TEXT);
    let second = encode(&session, second, TEXT);
    let (released_first, released_last) = if first_released_first {
        (&first, &second)
    } else {
        (&second, &first)
    };
    release(&session, released_first);
    assert!(!version.is_freed(), "the other lease keeps the version");
    release(&session, released_last);
    assert!(version.is_freed(), "the last release frees the version");
    session.close();
    project_session.close();
}

child_test! {
    fn two_leases_of_one_parse_first_released_first() {
        two_leases_of_one_parse(true);
    }
}

child_test! {
    fn two_leases_of_one_parse_second_released_first() {
        two_leases_of_one_parse(false);
    }
}

child_test! {
    // Go `Session.Close` releases the leases that are left
    // (api/session.go:4686 `releaseSourceFileLeases`). Their versions are
    // freed.
    fn session_close_frees_the_leases_that_are_left() {
        let (project_session, session) = setup();
        let versions: Vec<FileVersionProbe> = (2..5)
            .map(|n| {
                let text = format!("export const a = {n};\n");
                let lease = lease(&session, A_FILE, &text);
                let version = file_version_probe(lease.source_file())
                    .expect("a new parse of a published path is freeable");
                let _ = encode(&session, lease, &text);
                version
            })
            .collect();
        assert!(!versions.iter().any(FileVersionProbe::is_freed), "the leases keep the versions");
        session.close();
        assert!(versions.iter().all(FileVersionProbe::is_freed), "the close frees them");
        project_session.close();
    }
}

child_test! {
    // apimem1 problem 2b: a lease of a path that no program has and no
    // publish published. Its first version is freeable too, and the release
    // frees it.
    fn lease_of_a_new_path_is_freed() {
        let (project_session, session) = setup();
        encode_and_release(&session, "/home/projects/TS/p1/new.ts", "export const n = 1;\n");
        session.close();
        project_session.close();
    }
}

child_test! {
    // apimem1 problem 2 (sbm-loop): the plain API (`api --stdio`, Go
    // `NewStandaloneSession`) frees released leases, with no snapshot and no
    // program before them: the first lease of a path and a later one.
    fn standalone_session_frees_released_leases() {
        let (init, _) = projecttestutil::get_session_init_options(
            files(&[(A_FILE, A_TEXT)]),
            None,
            TypingsInstallerOptions::default(),
        );
        let session = api::new_standalone_session(&init, None);
        assert!(free_file_versions(), "an API process frees file versions");
        encode_and_release(&session, A_FILE, A_TEXT);
        encode_and_release(&session, A_FILE, "export const a = 2;\n");
        session.close();
    }
}
