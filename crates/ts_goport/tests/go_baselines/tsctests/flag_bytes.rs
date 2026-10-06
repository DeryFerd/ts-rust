//! Port-only test of the `tsgo --lsp` and `tsgo --api` flag errors. Go
//! writes the message with `fmt.Fprintln` (flag.go:1052), so a flag from the
//! OS keeps its bytes. The port holds an OS argument in the port form
//! (`vfs::go_string_from_os`), where a byte that is not valid UTF-8 is a
//! marker unit; the flag set's `output` writes the Go bytes. The expected
//! lines are Go N's (the pin N oracle, followups25 skeptic flagq2.py).
#![cfg(unix)]

use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;
use std::process::{Command, Stdio};

/// The first stderr line of `tsgo args`, which must exit 2.
fn first_stderr_line(args: &[&[u8]]) -> Vec<u8> {
    let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(args.iter().map(|arg| OsStr::from_bytes(arg)))
        .stdin(Stdio::null())
        .output()
        .expect("run tsgo");
    assert_eq!(output.status.code(), Some(2), "tsgo {args:?}");
    output
        .stderr
        .split(|&b| b == b'\n')
        .next()
        .unwrap_or_default()
        .to_vec()
}

// Go: flag/flag.go:1050 FlagSet.sprintf, from parseOne (:1093 and :1115).
#[test]
fn flag_errors_write_the_go_bytes() {
    assert_eq!(
        first_stderr_line(&[b"--lsp", b"-\xff=1"]),
        b"flag provided but not defined: -\xff"
    );
    assert_eq!(
        first_stderr_line(&[b"--lsp", b"-=\xff"]),
        b"bad flag syntax: -=\xff"
    );
    assert_eq!(
        first_stderr_line(&[b"--api", b"-x\xfey"]),
        b"flag provided but not defined: -x\xfey"
    );
}
