//! Port of Go `internal/api/session_batch_test.go` (ts#63937, ts#64061).
//!
//! PORT: the tests are in `project_lsp` because they use `projecttestutil`
//! and `child_test!`. A Go `defer ...Close()` is a call at the end of the
//! test, in the Go defer order.
//!
//! PORT: a Go `&Session{}` and a nil `*Session` have no Rust form (a session
//! always has a snapshot host). The two tests that use them run on an LSP
//! session of an empty `projecttestutil.Setup`, like the other tests here.
//!
//! PORT: the port only marshals `BatchRequestsResponse` (the server never
//! reads one). Go `json.Unmarshal(encoded, &wireResponse)` reads the page into
//! a generic JSON value (`LspAny`) here; its `result` is the Go `any`.

use indexmap::IndexMap;
use ts_goport::api::{
    self, BatchRequest, BatchRequestsParams, BatchRequestsResponse, BatchResponse, Method,
};
use ts_goport::frontend::json::{json_marshal, json_unmarshal};
use ts_goport::frontend::json_ext::{JsonValue, LspAny};

use super::api_util::{error_contains, nil_error};
use super::projecttestutil::{self, files};
use super::util::bg;

/// Go `BatchRequest{Method: method, Params: json.Value(params)}`.
fn batch_request(method: &str, params: &str) -> BatchRequest {
    BatchRequest {
        method: Method(method.to_string().into()),
        params: JsonValue(params.as_bytes().to_vec()),
    }
}

/// Go `response.Result` compared with a string (`assert.Equal(t, response.Result, "pong")`).
fn result_string(response: &BatchResponse) -> Option<&str> {
    response
        .result
        .as_deref()
        .and_then(|result| result.downcast_ref::<String>())
        .map(String::as_str)
}

/// Go `json.Marshal(response)` with `assert.NilError`.
fn marshal(response: &BatchRequestsResponse) -> String {
    json_marshal(response, &[]).unwrap_or_else(|err| panic!("marshal: {err:?}"))
}

/// Go `json.Unmarshal(encoded, &wireResponse)` with `assert.NilError` (see the file header).
fn unmarshal(encoded: &str) -> IndexMap<String, LspAny> {
    let mut wire = LspAny::default();
    json_unmarshal(encoded.as_bytes(), &mut wire, &[])
        .unwrap_or_else(|err| panic!("unmarshal: {err:?}"));
    match wire {
        LspAny::Object(object) => object,
        other => panic!("not an object: {other:?}"),
    }
}

// Go: session_batch_test.go:13 TestHandleBatchRequests
child_test! {
    fn handle_batch_requests() {
        // PORT: Go `&Session{}` (see the file header).
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);
        let response = session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: vec![batch_request("ping", ""), batch_request("unknown", "")],
                ..Default::default()
            },
        );

        let response = nil_error(response);
        assert_eq!(response.responses.len(), 2);
        assert_eq!(response.responses[0].method, Method("ping".into()));
        assert_eq!(result_string(&response.responses[0]), Some("pong"));
        assert_eq!(response.responses[0].error, "");
        assert_eq!(response.responses[1].method, Method("unknown".into()));
        let request_err = &response.responses[1].error;
        assert!(request_err.contains("unknown API method"));

        let encoded = marshal(&response);
        assert!(
            encoded.contains(r#""error":"api: invalid request: unknown API method \"unknown\"""#),
            "{encoded}"
        );
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:38 TestHandleBatchRequestsRecoversPerRequestPanics
// PORT: Go runs the requests on a nil `*Session`, so `getAnyType` panics when
// it reads `s.snapshotsMu`. A Rust session is never nil. Here the test holds
// the session's snapshot map while the batch runs, so `getAnyType` panics at
// the same read (`get_snapshot_data`) and `ping` does not.
child_test! {
    fn handle_batch_requests_recovers_per_request_panics() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);
        let snapshots = session.snapshots.borrow_mut();
        let response = session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: vec![
                    batch_request("ping", ""),
                    batch_request(
                        &api::Method::GET_ANY_TYPE.0,
                        r#"{"snapshot":1,"project":"project"}"#,
                    ),
                    batch_request("ping", ""),
                ],
                ..Default::default()
            },
        );
        drop(snapshots);

        let response = nil_error(response);
        assert_eq!(result_string(&response.responses[0]), Some("pong"));
        assert!(response.responses[1].error.contains("panic:"), "{}", response.responses[1].error);
        assert_eq!(result_string(&response.responses[2]), Some("pong"));
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:56 TestBatchResponseEncodesEmptyResult
#[test]
fn batch_response_encodes_empty_result() {
    let response = BatchResponse {
        method: api::Method::GET_SIGNATURES_OF_TYPE,
        result: Some(Box::new(Vec::<LspAny>::new())),
        ..Default::default()
    };
    let encoded = json_marshal(&response, &[]).unwrap_or_else(|err| panic!("marshal: {err:?}"));
    assert_eq!(encoded, r#"{"method":"getSignaturesOfType","result":[]}"#);
}

// Go: session_batch_test.go:64 TestHandleBatchRequestsPaginatesResponses
child_test! {
    fn handle_batch_requests_paginates_responses() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);

        const MAX_RESPONSE_BYTES_PER_PAGE: i32 = 150;
        let requests: Vec<BatchRequest> = (0..10).map(|_| batch_request("ping", "")).collect();

        let mut response = nil_error(session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: requests.clone(),
                max_response_bytes_per_page: MAX_RESPONSE_BYTES_PER_PAGE,
                ..Default::default()
            },
        ));
        let mut responses: Vec<LspAny> = Vec::new();
        loop {
            let encoded = marshal(&response);
            assert!(encoded.len() <= MAX_RESPONSE_BYTES_PER_PAGE as usize, "{encoded}");
            let wire_response = unmarshal(&encoded);
            if let Some(LspAny::Array(page)) = wire_response.get("responses") {
                responses.extend(page.iter().cloned());
            }
            let continuation_token = match wire_response.get("continuationToken") {
                Some(LspAny::String(token)) => token.clone(),
                _ => String::new(),
            };
            if continuation_token.is_empty() {
                break;
            }
            response = nil_error(session.handle_batch_requests(
                &bg(),
                &BatchRequestsParams {
                    continuation_token,
                    max_response_bytes_per_page: MAX_RESPONSE_BYTES_PER_PAGE,
                    ..Default::default()
                },
            ));
        }

        assert_eq!(responses.len(), requests.len());
        for response in &responses {
            let LspAny::Object(response) = response else {
                panic!("not an object: {response:?}");
            };
            assert_eq!(response.get("method"), Some(&LspAny::String("ping".to_string())));
            assert_eq!(response.get("result"), Some(&LspAny::String("pong".to_string())));
        }
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:107 TestHandleBatchRequestsAllowsOversizedSingleResponse
child_test! {
    fn handle_batch_requests_allows_oversized_single_response() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);

        let response = nil_error(session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: vec![batch_request("ping", "")],
                max_response_bytes_per_page: 1,
                ..Default::default()
            },
        ));
        assert_eq!(response.responses.len(), 1);
        assert_eq!(response.continuation_token, "");
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:124 TestHandleBatchRequestsPageLimitIsRequestScoped
child_test! {
    fn handle_batch_requests_page_limit_is_request_scoped() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);

        let requests = vec![batch_request("ping", ""), batch_request("ping", "")];

        let limited = nil_error(session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: requests.clone(),
                max_response_bytes_per_page: 1,
                ..Default::default()
            },
        ));
        assert_eq!(limited.responses.len(), 1);
        assert!(!limited.continuation_token.is_empty());

        let unlimited = nil_error(session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: requests.clone(),
                ..Default::default()
            },
        ));
        assert_eq!(unlimited.responses.len(), requests.len());
        assert_eq!(unlimited.continuation_token, "");
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:151 TestHandleBatchRequestsRejectsInvalidContinuationToken
child_test! {
    fn handle_batch_requests_rejects_invalid_continuation_token() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);

        error_contains(
            session.handle_batch_requests(
                &bg(),
                &BatchRequestsParams {
                    continuation_token: "invalid".to_string(),
                    ..Default::default()
                },
            ),
            "invalid batch continuation token",
        );
        session.close();
        project_session.close();
    }
}

// Go: session_batch_test.go:163 TestHandleBatchRequestsRejectsNestedBatch
child_test! {
    fn handle_batch_requests_rejects_nested_batch() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_lsp_session(project_session.clone(), None);

        let response = nil_error(session.handle_batch_requests(
            &bg(),
            &BatchRequestsParams {
                requests: vec![batch_request(&api::Method::BATCH_REQUESTS.0, r#"{"requests":[]}"#)],
                ..Default::default()
            },
        ));
        assert_eq!(response.responses.len(), 1);
        assert!(response.responses[0]
            .error
            .contains("batchRequests cannot be nested"));
        session.close();
        project_session.close();
    }
}
