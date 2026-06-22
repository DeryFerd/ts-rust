use std::{
    io::Write,
    process::{Command, Stdio},
};

fn frame(payload: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{payload}", payload.len())
}

#[test]
fn serves_an_lsp_session_over_stdio() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .arg("--lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let input = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]
    .into_iter()
    .map(frame)
    .collect::<String>();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();

    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "tsgo failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains(r#""id":1,"result":{"capabilities"#));
    assert!(stdout.contains(r#""textDocumentSync":{"openClose":true,"change":2}"#));
    assert!(stdout.contains(r#""id":2,"result":null"#));
    assert!(!stdout.contains("tsgo: TypeScript compiler"));
}
