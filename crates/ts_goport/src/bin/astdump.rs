//! `astdump -p <tsconfig> -o <outdir>`: writes the AST that the Go checker
//! sees through the ts_goport adapter, one dump per program file, in the
//! format of the Go tool `tools/tsgo-src/cmd/astdump`:
//!
//! `<depth> <Kind> <pos> <end> <flags hex> [lists]`
//!
//! Nodes are in pre-order (`for_each_child` order). `[lists]` holds the
//! non-nil NodeList/ModifierList slots as `L<pos>-<end>:<count>[,tc]`
//! (`M` for modifier lists). Eagerly parsed JSDoc is dumped under its host
//! as `@<depth> ...` lines. Compare both outputs with `diff` to find adapter
//! mismatches.

use std::fmt::Write as _;

use ts_goport::prelude::*;

fn list_str(prefix: &str, l: NodeList) -> String {
    let mut s = format!("{prefix}{}-{}:{}", l.pos(), l.end(), l.nodes().len());
    if l.has_trailing_comma() {
        s.push_str(",tc");
    }
    s
}

fn dump(out: &mut String, file: Node, n: Node, depth: usize, marker: &str) {
    let mut lists = Vec::new();
    let mut children = Vec::new();
    n.for_each_child_and_lists(
        &mut |c| {
            children.push(c);
            false
        },
        &mut |l, is_mod| lists.push(list_str(if is_mod { "M" } else { "L" }, l)),
    );
    let _ = write!(out, "{marker}{depth} {:?} {} {} {:x}", n.kind(), n.pos(), n.end(), n.flags().0);
    if !lists.is_empty() {
        let _ = write!(out, " [{}]", lists.join(" "));
    }
    out.push('\n');
    for j in n.eager_js_doc(file) {
        dump(out, file, j, depth + 1, "@");
    }
    for c in children {
        dump(out, file, c, depth + 1, marker);
    }
}

/// Output name: the path with '/' replaced by '!'; default libs use
/// `lib!<basename>` like the Go tool.
fn out_name(file: Node) -> String {
    let name = source_file_file_name(file);
    if file.go_file().source.is_default_library {
        return format!("lib!{}", name.rsplit('/').next().unwrap_or(name));
    }
    name.replace('/', "!")
}

fn run(project: &str, out_dir: &str) {
    if let Err(message) = try_load(project) {
        eprintln!("astdump: {message}");
        std::process::exit(1);
    }
    std::fs::create_dir_all(out_dir).expect("create output directory");
    for file in source_files() {
        let mut out = String::new();
        dump(&mut out, file, file, 0, "");
        std::fs::write(format!("{out_dir}/{}", out_name(file)), out).expect("write dump");
        println!("{}", source_file_file_name(file));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut project, mut out_dir) = (None, None);
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "-p" => project = iter.next(),
            "-o" => out_dir = iter.next(),
            _ => {}
        }
    }
    let (Some(project), Some(out_dir)) = (project, out_dir) else {
        eprintln!("usage: astdump -p <tsconfig> -o <outdir>");
        std::process::exit(1);
    };
    // Program state is thread-local; run on one big-stack thread like goport.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || run(&project, &out_dir))
        .expect("spawn")
        .join()
        .expect("astdump thread failed");
}
