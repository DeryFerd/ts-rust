//! PORT: no Go counterpart (effectapi1). Effect-TS/tsgo runs the Effect
//! rules in every checker, so its API answers carry Effect diagnostics. A
//! port standalone API process (`api::new_standalone_session`, `tsgo --api`)
//! answers as plain tsgo, unless `TSGO_EFFECT_API=1`
//! (`effect::rulerunner::set_api_process`). The language server keeps the
//! rules, also for an API session inside it, which shares its checkers.
//!
//! The fixture needs no Effect package: `globalDate` (TS377068) flags
//! `new Date()`, and the plugin option check flags the unknown rule name
//! in the config diagnostics (`unknownRuleName`).

use std::rc::Rc;

use ts_goport::api::{
    self, CreateSnapshotParams, GetDefaultProjectForFileParams, GetDiagnosticsParams,
    GetProjectDiagnosticsParams, SnapshotRequestChangesParams,
};
use ts_goport::effect::diag;
use ts_goport::program::ls_program;

use super::api_util::{doc, nil_error};
use super::projecttestutil::{self, TypingsInstallerOptions, files};
use super::util::{bg, open, program};

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const INDEX: &str = "/home/projects/p/index.ts";
const CONFIG_TEXT: &str = r#"{"compilerOptions":{"strict":true,"plugins":[{"name":"@effect/language-service","diagnosticSeverity":{"globalDate":"error","noSuchRule":"error"}}]}}"#;
const INDEX_TEXT: &str = "export const value: string = 42;\nexport const date = new Date();\n";

const TS2322: i32 = 2322;
const GLOBAL_DATE: i32 = 377_068;

fn unknown_rule_name() -> i32 {
    let message =
        diag::Unknown_Effect_diagnostic_rule_0_in_diagnosticSeverity_effect_unknownRuleName;
    i32::try_from(message.code()).expect("an i32 code")
}

/// The codes of the semantic diagnostics of index.ts and of the config
/// diagnostics, as `session` answers them.
fn api_codes(session: &api::Session) -> (Vec<i32>, Vec<i32>) {
    let ctx = bg();
    let snapshot = nil_error(session.handle_create_snapshot(
        &ctx,
        &CreateSnapshotParams {
            snapshot_request_changes_params: SnapshotRequestChangesParams {
                open_projects: vec![doc(CONFIG)],
                ..Default::default()
            },
            ..Default::default()
        },
    ))
    .snapshot;
    let project = nil_error(session.handle_get_default_project_for_file(
        &ctx,
        &GetDefaultProjectForFileParams {
            snapshot,
            file: doc(INDEX),
        },
    ))
    .expect("a default project")
    .id;
    let semantic = nil_error(session.handle_get_semantic_diagnostics(
        &ctx,
        &GetDiagnosticsParams {
            snapshot,
            project: project.clone(),
            files: Some(vec![doc(INDEX)]),
        },
    ));
    let config = nil_error(session.handle_get_config_file_parsing_diagnostics(
        &ctx,
        &GetProjectDiagnosticsParams { snapshot, project },
    ));
    (
        semantic.iter().map(|d| d.code).collect(),
        config.iter().map(|d| d.code).collect(),
    )
}

/// `api_codes` for a standalone API session on the fixture.
fn standalone_codes() -> (Vec<i32>, Vec<i32>) {
    let (init, _) = projecttestutil::get_session_init_options(
        files(&[(CONFIG, CONFIG_TEXT), (INDEX, INDEX_TEXT)]),
        None,
        TypingsInstallerOptions::default(),
    );
    let session = api::new_standalone_session(&init, None);
    let codes = api_codes(&session);
    session.close();
    codes
}

child_test! {
    fn standalone_api_answers_without_effect_rules() {
        assert_eq!(standalone_codes(), (vec![TS2322], vec![]));
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "1")];
    fn standalone_api_with_effect_api_answers_as_the_reference() {
        assert_eq!(
            standalone_codes(),
            (vec![TS2322, GLOBAL_DATE], vec![unknown_rule_name()])
        );
    }
}

child_test! {
    fn language_server_keeps_effect_rules() {
        let (project_session, _) =
            projecttestutil::setup(files(&[(CONFIG, CONFIG_TEXT), (INDEX, INDEX_TEXT)]));
        open(&project_session, &format!("file://{INDEX}"), INDEX_TEXT);
        let p = program(&project_session, &format!("file://{INDEX}"));
        let file = p.get_source_file(INDEX).expect("index.ts");
        let semantic: Vec<i32> = ls_program::get_semantic_diagnostics(
            &p,
            &projecttestutil::with_request_id(&bg()),
            file.root,
        )
        .iter()
        .map(|d| d.code())
        .collect();
        let config: Vec<i32> = p
            .get_config_file_parsing_diagnostics()
            .iter()
            .map(|d| d.code())
            .collect();
        assert_eq!((semantic, config), (vec![TS2322, GLOBAL_DATE], vec![unknown_rule_name()]));

        // An API session in the server shares its checkers and keeps the rules.
        let session = api::new_lsp_session(Rc::clone(&project_session), None);
        assert_eq!(
            api_codes(&session),
            (vec![TS2322, GLOBAL_DATE], vec![unknown_rule_name()])
        );
        session.close();
        project_session.close();
    }
}
