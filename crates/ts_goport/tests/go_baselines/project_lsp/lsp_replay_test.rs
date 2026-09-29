//! Port of Go `internal/lsp/replay_test.go`.
//!
//! PORT: Go reads the `-replay`, `-testDir`, `-simple` and `-superSimple`
//! test flags. libtest has no custom flags, so they are the environment
//! variables `TS_GOPORT_REPLAY`, `TS_GOPORT_REPLAY_TEST_DIR`,
//! `TS_GOPORT_REPLAY_SIMPLE=1` and `TS_GOPORT_REPLAY_SUPER_SIMPLE=1`. As in
//! Go, the test does nothing (Go skips) when no replay file is given.
//! The server uses the OS file system, so this is a plain `#[test]`, not a
//! `child_test!`.

use ts_goport::frontend::json::{
    JsonDecoder, JsonError, UnmarshalerFrom, append_json_quote, json_unmarshal,
    json_unmarshal_decode,
};
use ts_goport::frontend::json_ext::{JsonValue, unmarshal_struct_fields};
use ts_goport::jsonrpc;
use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::lsptestutil;

// Go: replay_test.go:28 initialArguments
#[derive(Default)]
struct InitialArguments {
    root_dir_uri_placeholder: String,
    root_dir_placeholder: String,
}

impl UnmarshalerFrom for InitialArguments {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "initialArguments", |name, dec| {
            match name {
                "rootDirUriPlaceholder" => {
                    json_unmarshal_decode(dec, &mut self.root_dir_uri_placeholder)?
                }
                "rootDirPlaceholder" => json_unmarshal_decode(dec, &mut self.root_dir_placeholder)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = InitialArguments::default();
        }
        Ok(())
    }
}

// Go: replay_test.go:33 rawMessage
#[derive(Clone, Default)]
struct RawMessage {
    kind: String,
    method: String,
    params: JsonValue,
}

impl UnmarshalerFrom for RawMessage {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "rawMessage", |name, dec| {
            match name {
                "kind" => json_unmarshal_decode(dec, &mut self.kind)?,
                "method" => json_unmarshal_decode(dec, &mut self.method)?,
                "params" => json_unmarshal_decode(dec, &mut self.params)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = RawMessage::default();
        }
        Ok(())
    }
}

fn flag(name: &str) -> String {
    std::env::var(name).unwrap_or_default()
}

fn bool_flag(name: &str) -> bool {
    matches!(flag(name).as_str(), "1" | "true")
}

// Go: replay_test.go:220 isInitializationMessage
fn is_initialization_message(msg: &RawMessage) -> bool {
    msg.method == "initialize" || msg.method == "initialized"
}

// Go: replay_test.go:224 isExitMessage
fn is_exit_message(msg: &RawMessage) -> bool {
    msg.method == "exit" || msg.method == "shutdown"
}

/// Go `for i = 0; i < len(messages) && isInitializationMessage(messages[i]); i++`
/// and `for j = len(messages) - 1; j >= 0 && isExitMessage(messages[j]); j--`.
fn init_and_last(messages: &[RawMessage]) -> (isize, isize) {
    let i = messages
        .iter()
        .take_while(|m| is_initialization_message(m))
        .count() as isize;
    let mut j = messages.len() as isize - 1;
    while j >= 0 && is_exit_message(&messages[j as usize]) {
        j -= 1;
    }
    (i, j)
}

// Go: replay_test.go:123 (the `simple` branch)
// Include only initialization, file opening/changing/closing, and shutdown messages, plus the final request.
fn simple_messages(messages: &[RawMessage]) -> Vec<RawMessage> {
    let (i, j) = init_and_last(messages);
    let mut new_messages: Vec<RawMessage> = messages[..i as usize].to_vec();
    for k in i..=j {
        let msg = &messages[k as usize];
        if matches!(
            msg.method.as_str(),
            "textDocument/didOpen" | "textDocument/didChange" | "textDocument/didClose"
        ) {
            new_messages.push(msg.clone());
        }
    }
    new_messages.extend_from_slice(&messages[i.max(j) as usize..]);
    new_messages
}

// Go: replay_test.go:143 (the `superSimple` branch)
// Include only initialization, shutdown, the last file open and the final request.
// We assume here the final request will be for the file that was opened last.
fn super_simple_messages(messages: &[RawMessage]) -> Vec<RawMessage> {
    let (i, j) = init_and_last(messages);
    let mut new_messages: Vec<RawMessage> = messages[..i as usize].to_vec();
    let mut open_idx = j;
    while open_idx >= i {
        let msg = &messages[open_idx as usize];
        if msg.method == "textDocument/didOpen" {
            new_messages.push(msg.clone());
            break;
        }
        open_idx -= 1;
    }
    new_messages.extend_from_slice(&messages[(open_idx + 1).max(j).max(0) as usize..]);
    new_messages
}

// Go: replay_test.go:40 TestReplay
#[test]
fn test_replay() {
    let replay = flag("TS_GOPORT_REPLAY");
    if replay.is_empty() {
        eprintln!("no replay file specified");
        return;
    }
    let test_dir = flag("TS_GOPORT_REPLAY_TEST_DIR");
    if test_dir.is_empty() {
        panic!("testDir must be specified");
    }
    let test_dir_uri = lsconv::file_name_to_document_uri(&test_dir);

    let cwd = std::env::current_dir()
        .expect("getwd")
        .to_string_lossy()
        .into_owned();
    let mut client = lsptestutil::new_lsp_client(lsptestutil::os_server_setup(&cwd), None, None);

    let text = std::fs::read_to_string(&replay)
        .unwrap_or_else(|err| panic!("failed to read replay file: {err}"));
    let mut lines = text.lines();
    let first_line = lines
        .next()
        .unwrap_or_else(|| panic!("replay file is empty"));

    let mut init_obj = InitialArguments::default();
    json_unmarshal(first_line.as_bytes(), &mut init_obj, &[])
        .unwrap_or_else(|err| panic!("failed to parse initial arguments: {}", err.message));
    let mut root_dir_placeholder = "@PROJECT_ROOT@".to_string();
    let mut root_dir_uri_placeholder = "@PROJECT_ROOT_URI@".to_string();
    if !init_obj.root_dir_placeholder.is_empty() {
        root_dir_placeholder = init_obj.root_dir_placeholder;
    }
    if !init_obj.root_dir_uri_placeholder.is_empty() {
        root_dir_uri_placeholder = init_obj.root_dir_uri_placeholder;
    }

    let mut messages = Vec::new();
    for line in lines {
        // Go: strings.NewReplacer(rootDirPlaceholder, testDir, rootDirUriPlaceholder, testDirUri)
        let line = line
            .replace(&root_dir_placeholder, &test_dir)
            .replace(&root_dir_uri_placeholder, &test_dir_uri.0);
        let mut raw_msg = RawMessage::default();
        json_unmarshal(line.as_bytes(), &mut raw_msg, &[])
            .unwrap_or_else(|err| panic!("failed to parse message: {}", err.message));
        messages.push(raw_msg);
    }

    if bool_flag("TS_GOPORT_REPLAY_SIMPLE") {
        messages = simple_messages(&messages);
    } else if bool_flag("TS_GOPORT_REPLAY_SUPER_SIMPLE") {
        messages = super_simple_messages(&messages);
    }

    for raw_msg in &messages {
        let req_id = match raw_msg.kind.as_str() {
            "request" => Some(client.next_id()),
            "notification" => None,
            kind => panic!("unknown message kind: {kind}"),
        };

        // Go: json.Marshal of struct{JSONRPC, ID *jsonrpc.ID, Method, Params json.Value}.
        let mut rpc_data = String::from(r#"{"jsonrpc":"2.0","id":"#);
        match req_id {
            Some(id) => rpc_data.push_str(&id.to_string()),
            None => rpc_data.push_str("null"),
        }
        rpc_data.push_str(r#","method":"#);
        append_json_quote(&mut rpc_data, &raw_msg.method);
        rpc_data.push_str(r#","params":"#);
        if raw_msg.params.0.is_empty() {
            rpc_data.push_str("null");
        } else {
            rpc_data.push_str(&String::from_utf8_lossy(&raw_msg.params.0));
        }
        rpc_data.push('}');

        let mut msg = lsproto::Message::default();
        msg.unmarshal_json(rpc_data.as_bytes())
            .unwrap_or_else(|err| {
                panic!(
                    "failed to unmarshal rpc message into lsproto.Message: {}",
                    err.error()
                )
            });

        match req_id {
            Some(id) => {
                let response = client
                    .send_request_worker(msg.into_request(), jsonrpc::new_id_int(id))
                    .unwrap_or_else(|| {
                        panic!("failed to send request for method {}", raw_msg.method)
                    });
                if let Some(error) = &response.error {
                    // Go `%s` of a nil json.Value is "null" (Value.String).
                    let params = match raw_msg.params.0.as_slice() {
                        [] => "null".into(),
                        bytes => String::from_utf8_lossy(bytes),
                    };
                    panic!(
                        "server returned error for method {} params {params}:\n[{}]: {}",
                        raw_msg.method, error.code, error.message
                    );
                }
            }
            None => client.write_msg(msg),
        }
    }

    if let Err(err) = client.close() {
        panic!("goroutine error: {}", err.error());
    }
}
