//! PORT: no Go counterpart (csfree1 follow-up, R173 reviewer item 9). The
//! stdio API shape of csfree1 (the skeptic's sk-min-stdio-static trace):
//! `tsgo --api` makes a standalone session (Go `NewStandaloneSession`), whose
//! own snapshot host gives its snapshot programs and `createSourceFile` one
//! parse cache. A lease of the disk text shares the parse of the first
//! snapshot's program. An update changes the file, and the release of the
//! first snapshot releases its program. A second lease of the disk text then
//! gets the parse that only the first lease keeps in the parse cache. Go
//! encodes both from one `*ast.SourceFile` (api/session.go:1876
//! encodeLeasedSourceFile), so the two answers differ only in the lease id.

use std::rc::Rc;
use ts_goport::api::encoder::encoder::encode_parsed_source_file;
use ts_goport::api::requestfilesystem::{Kind, RequestFileSystem};
use ts_goport::api::{
    self, CreateSnapshotParams, CreateSourceFileOptions, EnsurePrograms, FileNotifications,
    ReleaseParams, ReleaseSourceFileParams, SnapshotID, SnapshotRequestChangesParams,
    SourceFileLeaseID, SourceFileResponse, UpdateSnapshotParams,
};
use ts_goport::core::Node;
use ts_goport::frontend::parser::ParsedSourceFile;
use ts_goport::program::ls_program;

use super::api_util::{doc, nil_error, project_program, snapshot_of};
use super::projecttestutil::{self, TypingsInstallerOptions, files};
use super::requestfilesystem_test::files as request_files;
use super::util::bg;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const INDEX_FILE: &str = "/home/projects/p/index.ts";
const A_FILE: &str = "/home/projects/p/a.ts";
const A_TEXT: &str = "export const a = 1;";

/// Encodes a lease of `A_TEXT` at a.ts, as `handleCreateSourceFile` does,
/// and checks the header as Go writes it: bytes 4-11 are `Hash.Lo` and
/// 12-19 `Hash.Hi` of the parse cache hash, the xxh3-128 of the text
/// (project/parsecache.go:79, encoder.go:629-630), and bytes 20-23 the zero
/// parse option bits of a lease (session.go:1866-1869, encoder.go:631).
/// Returns the root of the leased file and the bytes.
fn create_source_file(session: &api::Session) -> (Node, Vec<u8>) {
    let lease =
        nil_error(session.create_source_file(A_FILE, A_TEXT, &CreateSourceFileOptions::default()));
    let root = lease.source_file();
    let answer = nil_error(session.encode_leased_source_file(lease)).expect("an answer");
    let response = answer
        .downcast_ref::<SourceFileResponse>()
        .expect("a SourceFileResponse: a stdio session answers in base64");
    let data = nil_error(api::base64_std_encoding_decode_string(&response.data));
    let hash = xxhash_rust::xxh3::xxh3_128(A_TEXT.as_bytes());
    assert_eq!(data[4..12], (hash as u64).to_le_bytes(), "Hash.Lo");
    assert_eq!(data[12..20], ((hash >> 64) as u64).to_le_bytes(), "Hash.Hi");
    assert_eq!(data[20..24], [0; 4], "the parse option bits");
    (root, data)
}

/// The lease id in the header (bytes 52-59, Go `SetSourceFileLease`).
fn lease_id(data: &[u8]) -> SourceFileLeaseID {
    SourceFileLeaseID(u64::from_le_bytes(data[52..60].try_into().unwrap()))
}

/// The root of the parse of a.ts in the program of `snapshot`, and its text.
fn program_parse(session: &api::Session, snapshot: SnapshotID) -> (Node, String) {
    let program = project_program(&snapshot_of(session, snapshot), CONFIG);
    let file = program
        .get_source_file(A_FILE)
        .expect("a.ts is in the program");
    (file.root, file.text.to_string())
}

child_test! {
    fn lease_of_a_program_parse_after_the_snapshot_release() {
        let (init, _) = projecttestutil::get_session_init_options(
            files(&[
                (CONFIG, r#"{"compilerOptions":{"noLib":true}}"#),
                (INDEX_FILE, "import { a } from './a';\nexport const x = a + 1;"),
                (A_FILE, A_TEXT),
            ]),
            None,
            TypingsInstallerOptions::default(),
        );
        let session = api::new_standalone_session(&init, None);
        let first = nil_error(session.handle_create_snapshot(
            &bg(),
            &CreateSnapshotParams {
                snapshot_request_changes_params: SnapshotRequestChangesParams {
                    open_projects: vec![doc(CONFIG)],
                    ..Default::default()
                },
                ..Default::default()
            },
        ))
        .snapshot;

        let (loaded, _) = program_parse(&session, first);
        let (root, before) = create_source_file(&session);
        assert_eq!(root, loaded, "the lease shares the program's parse");
        assert!(ls_program::program_parsed_source_file(root).is_some());

        let second = nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                snapshot: first,
                changes: Some(CreateSnapshotParams {
                    snapshot_request_changes_params: SnapshotRequestChangesParams {
                        ensure_programs: Some(EnsurePrograms {
                            all: true,
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                    file_system: Some(RequestFileSystem {
                        kind: Kind::LAYER,
                        files: request_files(&[(A_FILE, "export const a = 2;")]),
                        ..Default::default()
                    }),
                    file_notifications: Some(FileNotifications {
                        changed: vec![doc(A_FILE)],
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
            },
        ))
        .snapshot;
        assert_eq!(program_parse(&session, second).1, "export const a = 2;");
        nil_error(session.handle_release(&bg(), Some(&ReleaseParams { snapshot: first })));
        assert!(
            ls_program::program_parsed_source_file(root).is_none(),
            "no live program has the parse"
        );

        let (again, after) = create_source_file(&session);
        assert_eq!(again, root, "the parse cache gives the leased parse");
        assert_ne!(lease_id(&before), lease_id(&after));
        assert_eq!(before[..52], after[..52]);
        assert_eq!(before[60..], after[60..]);
        for data in [&before, &after] {
            nil_error(session.handle_release_source_file(Some(&ReleaseSourceFileParams {
                lease: lease_id(data),
            })));
        }
        session.close();
    }
}

// The encode of a lease reads the Go `SourceFile` fields that the parser
// sets from the record that the lease holds, as Go reads them from the
// leased `*ast.SourceFile` (api/encoder/encoder.go:603
// `encodeStringArray(sf.AmbientModuleNames, ...)`), and not from the
// published `GoFile` of the program that shares the parse (R173 reviewer
// item 9). In a real lease the two have the same lists, so the test gives
// the encoder a copy of the lease's record with one more ambient module
// name: the answer has it. An encode that reads the `GoFile` does not.
child_test! {
    fn lease_encode_reads_the_parser_fields_of_the_lease() {
        const PROBE: &str = "item9-ambient-probe";
        let (init, _) = projecttestutil::get_session_init_options(
            files(&[
                (CONFIG, r#"{"compilerOptions":{"noLib":true}}"#),
                (INDEX_FILE, "import { a } from './a';\nexport const x = a + 1;"),
                (A_FILE, A_TEXT),
            ]),
            None,
            TypingsInstallerOptions::default(),
        );
        let session = api::new_standalone_session(&init, None);
        let snapshot = nil_error(session.handle_create_snapshot(
            &bg(),
            &CreateSnapshotParams {
                snapshot_request_changes_params: SnapshotRequestChangesParams {
                    open_projects: vec![doc(CONFIG)],
                    ..Default::default()
                },
                ..Default::default()
            },
        ))
        .snapshot;
        let (loaded, _) = program_parse(&session, snapshot);
        let lease =
            nil_error(session.create_source_file(A_FILE, A_TEXT, &CreateSourceFileOptions::default()));
        assert_eq!(lease.source_file(), loaded, "the lease shares the program's parse");

        let mut record = ParsedSourceFile::clone(lease.parsed_source_file());
        record.ambient_module_names.push(PROBE.to_string());
        let (changed, _) = nil_error(encode_parsed_source_file(&Rc::new(record)));
        let (plain, _) = nil_error(encode_parsed_source_file(lease.parsed_source_file()));
        let has_probe = |data: &[u8]| data.windows(PROBE.len()).any(|w| w == PROBE.as_bytes());
        assert!(has_probe(&changed), "the encode reads the lease's record");
        assert!(!has_probe(&plain));
        lease.release();
        session.close();
    }
}
