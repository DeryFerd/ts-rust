//! The wasm build packs the bundled libs and the diagnostic message texts.
//! For a wasm target, this writes:
//! - the `crates/ts_goport/libs/lib.*.d.ts` files (not with `noembed`) as one
//!   LZMA stream to `OUT_DIR/libs.lzma`, and their paths and sizes in stream
//!   order to `OUT_DIR/libs.rs`. `src/frontend/bundled/embed.rs` unpacks the
//!   stream up to the last lib that a run reads. One stream is 0.31 MB, where
//!   one stream per lib was 0.48 MB: lib.webworker.d.ts repeats much of
//!   lib.dom.d.ts.
//! - the texts of `src/diagnostics/catalog.rs`, in catalog order and ended
//!   by NUL, as one LZMA stream to `OUT_DIR/diagnostic_texts.lzma`.
//!   `src/diagnostics/mod.rs` unpacks it on the first text read: 44 KB, not
//!   151 KB.
//!
//! Native builds embed the texts as they are, so this does nothing for them.

mod catalog_texts;

use lzma_rust2::{EncodeMode, LzmaOptions, LzmaWriter, MfType};
use std::io::Write;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() != Ok("wasm") {
        return;
    }
    pack_diagnostic_texts();
    if std::env::var_os("CARGO_FEATURE_NOEMBED").is_some() {
        return;
    }
    pack_libs();
}

/// Packs the libs into one stream. The webworker libs come last, so a run
/// that reads none of them (most do not) unpacks 3.0 of the 3.79 MB. Most
/// programs read lib.dom.d.ts and nearly all the other libs.
fn pack_libs() {
    let libs = PathBuf::from(env("CARGO_MANIFEST_DIR")).join("../../libs");
    println!("cargo:rerun-if-changed={}", libs.display());
    let mut names: Vec<String> = std::fs::read_dir(&libs)
        .expect("read crates/ts_goport/libs")
        .map(|entry| entry.expect("read crates/ts_goport/libs").file_name())
        .filter_map(|name| name.into_string().ok())
        .filter(|name| name.starts_with("lib.") && name.ends_with(".d.ts"))
        .collect();
    let webworker =
        |name: &str| name.starts_with("lib.webworker.") && name != "lib.webworker.importscripts.d.ts";
    names.sort_by(|a, b| (webworker(a), a).cmp(&(webworker(b), b)));
    let mut texts = Vec::new();
    let mut index = String::from("static PACKED_LIBS: &[(&str, usize)] = &[\n");
    for name in &names {
        let path = libs.join(name);
        println!("cargo:rerun-if-changed={}", path.display());
        let text = std::fs::read(path).expect("read a lib");
        index.push_str(&format!("    (\"libs/{name}\", {}),\n", text.len()));
        texts.extend_from_slice(&text);
    }
    index.push_str("];\n");
    let out = PathBuf::from(env("OUT_DIR"));
    std::fs::write(out.join("libs.lzma"), pack(&texts)).expect("write the libs");
    std::fs::write(out.join("libs.rs"), index).expect("write the lib index");
}

/// Packs the message texts of the generated catalog (`catalog_texts`).
fn pack_diagnostic_texts() {
    let catalog = PathBuf::from(env("CARGO_MANIFEST_DIR")).join("../../src/diagnostics/catalog.rs");
    println!("cargo:rerun-if-changed={}", catalog.display());
    let source = std::fs::read_to_string(&catalog).expect("read the diagnostic catalog");
    let out = PathBuf::from(env("OUT_DIR")).join("diagnostic_texts.lzma");
    std::fs::write(out, pack(catalog_texts::catalog_texts(&source).as_bytes()))
        .expect("write the diagnostic texts");
}

fn env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("cargo sets {name}"))
}

/// `text` as an `.lzma` stream with its size in the header, which
/// `LzmaReader::new_mem_limit` reads. The dictionary holds the whole text.
/// lc 0, pb 0 and the longest match length gave the smallest libs (one
/// stream per lib: 478 KB; xz -9e gave 484 KB).
fn pack(text: &[u8]) -> Vec<u8> {
    let len = u32::try_from(text.len()).expect("a text under 4 GB");
    let options = LzmaOptions::new(
        len.next_power_of_two().max(4096),
        0,
        0,
        0,
        EncodeMode::Normal,
        LzmaOptions::NICE_LEN_MAX,
        MfType::Bt4,
        512,
    );
    let mut writer = LzmaWriter::new_use_header(Vec::new(), &options, Some(u64::from(len)))
        .expect("start an LZMA stream");
    writer.write_all(text).expect("pack a text");
    writer.finish().expect("pack a text")
}
