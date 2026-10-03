//! The message texts of the generated diagnostic catalog
//! (`src/diagnostics/catalog.rs`), for the wasm build (`build.rs`). A test
//! in `src/diagnostics/mod.rs` checks it against the catalog.

/// The texts of the catalog source `source`, in catalog order, each ended
/// by NUL. Each `Message::catalog(` call has its arguments on their own
/// lines; the text is the fourth. The generator escapes only `"` and `\\`.
pub fn catalog_texts(source: &str) -> String {
    let mut texts = String::new();
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        if line.trim() != "Message::catalog(" {
            continue;
        }
        let literal = lines
            .nth(3)
            .and_then(|line| line.trim().strip_prefix('"')?.strip_suffix("\","))
            .expect("a catalog text is a string literal");
        let mut chars = literal.chars();
        while let Some(c) = chars.next() {
            texts.push(match c {
                '\\' => match chars.next() {
                    Some(c @ ('"' | '\\')) => c,
                    other => panic!("escape {other:?} in a catalog text"),
                },
                c => c,
            });
        }
        texts.push('\0');
    }
    texts
}
