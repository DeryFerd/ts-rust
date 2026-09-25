//! P1 gate for build mode: parse every `.tsbuildinfo` given on the command
//! line (files or directories), marshal it again and compare the bytes.
//! `cargo run --release -p ts_goport --example buildinfo_roundtrip -- <paths>`

use ts_goport::execute::incremental::incremental::{marshal_build_info, parse_build_info};

fn collect(path: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    if path.is_dir() {
        for entry in std::fs::read_dir(path).unwrap() {
            collect(&entry.unwrap().path(), out);
        }
    } else if path.extension().is_some_and(|e| e == "tsbuildinfo") {
        out.push(path.to_path_buf());
    }
}

fn main() {
    let mut files = Vec::new();
    for arg in std::env::args().skip(1) {
        collect(std::path::Path::new(&arg), &mut files);
    }
    let mut failures = 0;
    for path in &files {
        let text = std::fs::read_to_string(path).unwrap();
        let ok = parse_build_info(&text)
            .and_then(|info| marshal_build_info(&info).ok())
            .is_some_and(|out| out == text);
        if !ok {
            failures += 1;
            println!("FAIL {}", path.display());
        }
    }
    println!("checked {} files, {failures} failures", files.len());
    std::process::exit(i32::from(failures > 0));
}
