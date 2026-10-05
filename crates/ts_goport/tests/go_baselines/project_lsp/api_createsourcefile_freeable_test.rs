//! PORT: no Go counterpart (editfuzz4 G2, lane csfree1). In a language
//! server process a new parse of a path that the server published is a
//! freeable file version (`ast::freeable_path`, lsshells M3a). An api
//! `createSourceFile` or `createSourceFileFromFile` in an LSP-attached
//! session makes such a parse for a project file with new text or another
//! script kind, and for the open file with new text. Go encodes the leased
//! file (api/encoder/encoder.go:596 reads its `ParseOptions()`). The port
//! finds the parse while the lease keeps it alive, and its weak entry does
//! not keep the version after the release.

use std::rc::Rc;

use ts_goport::api::{
    self, CreateSourceFileFromFileParams, CreateSourceFileOptions, ReleaseSourceFileParams,
};
use ts_goport::ast::{file_version_probe, free_file_versions, release_file_version_pins};
use ts_goport::flags::ScriptKind;
use ts_goport::program::ls_program;
use ts_goport::project;

use super::api_util::nil_error;
use super::projecttestutil::{self, files};
use super::util::{bg, open, program};

const INDEX_URI: &str = "file:///home/projects/TS/p1/index.ts";
const INDEX_FILE: &str = "/home/projects/TS/p1/index.ts";
const INDEX_TEXT: &str = "import { a } from './a';\nexport const x = a + 1;";
const A_FILE: &str = "/home/projects/TS/p1/a.ts";

/// A project session with index.ts open and its program loaded, so the
/// server published index.ts and a.ts, and its API session.
fn setup() -> (Rc<project::Session>, Rc<api::Session>) {
    let (project_session, _) = projecttestutil::setup(files(&[
        ("/home/projects/TS/p1/tsconfig.json", "{}"),
        (INDEX_FILE, INDEX_TEXT),
        (A_FILE, "export const a = 1;"),
    ]));
    open(&project_session, INDEX_URI, INDEX_TEXT);
    let _ = program(&project_session, INDEX_URI);
    assert!(
        free_file_versions(),
        "a session process frees file versions"
    );
    let session = api::new_lsp_session(project_session.clone(), None);
    (project_session, session)
}

/// Encodes a new parse of `file_name` with `text` through a lease, as
/// `handleCreateSourceFile` does. The parse is a freeable version, and the
/// encoder finds it while the lease lives. After the release, the encoder's
/// reads pin the version on this thread until the next program release
/// (`release_file_version_pins`). Then it dies.
fn encode_and_release(session: &api::Session, file_name: &str, text: &str) {
    let lease =
        nil_error(session.create_source_file(file_name, text, &CreateSourceFileOptions::default()));
    let root = lease.source_file();
    let version = file_version_probe(root).expect("a new parse of a published path is freeable");
    assert!(ls_program::parsed_source_file(root).is_some_and(|parsed| parsed.root == root));
    assert!(nil_error(session.encode_leased_source_file(lease)).is_some());

    let id = *session
        .source_file_leases
        .borrow()
        .keys()
        .next()
        .expect("the encoded lease");
    nil_error(session.handle_release_source_file(Some(&ReleaseSourceFileParams { lease: id })));
    release_file_version_pins();
    assert!(version.is_freed(), "the lookup keeps the released version");
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
        let result = nil_error(session.handle_create_source_file_from_file(
            &bg(),
            &CreateSourceFileFromFileParams {
                file_name: A_FILE.to_string(),
                options: CreateSourceFileOptions {
                    script_kind: ScriptKind::JSX,
                },
            },
        ));
        assert!(result.is_some());
        session.close();
        project_session.close();
    }
}
