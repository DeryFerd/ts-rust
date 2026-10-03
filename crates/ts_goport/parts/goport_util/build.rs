//! The wasm build packs the bundled libs and the diagnostic message texts.
//! For a wasm target, this writes:
//! - each `crates/ts_goport/libs/lib.*.d.ts` (not with `noembed`) as an
//!   LZMA stream to `OUT_DIR/libs/<name>.lzma`. `src/frontend/bundled/embed.rs`
//!   embeds these and unpacks a lib on its first read. The packed libs are
//!   0.48 MB, not 3.79 MB.
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
    let libs = PathBuf::from(env("CARGO_MANIFEST_DIR")).join("../../libs");
    println!("cargo:rerun-if-changed={}", libs.display());
    let out = PathBuf::from(env("OUT_DIR")).join("libs");
    std::fs::create_dir_all(&out).expect("create OUT_DIR/libs");
    for entry in std::fs::read_dir(&libs).expect("read crates/ts_goport/libs") {
        let path = entry.expect("read crates/ts_goport/libs").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if name.starts_with("lib.") && name.ends_with(".d.ts") {
            let text = std::fs::read(&path).expect("read a lib");
            std::fs::write(out.join(format!("{name}.lzma")), pack(&text)).expect("write a lib");
        }
    }
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
/// lc 0, pb 0 and the longest match length gave the smallest total for
/// these libs (478 KB; xz -9e gives 484 KB).
fn pack(text: &[u8]) -> Vec<u8> {
    let len = u32::try_from(text.len()).expect("a lib under 4 GB");
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
    writer.write_all(text).expect("pack a lib");
    writer.finish().expect("pack a lib")
}
