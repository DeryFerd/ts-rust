//! Port of `github.com/peter-evans/patience` v0.3.0 (patience.go, lcs.go,
//! unified.go, format.go), the diff that Go `baseline.DiffText` uses, and Go
//! `stringutil.SplitLines`.
//!
//! PORT: the lines borrow the input text (`&str`) instead of copying Go
//! strings. The inputs are port form strings (see
//! `ts_goport::scanner_util::GO_STRING_MARKER`); `\r` and `\n` never occur
//! inside a port form unit, so line splits match the Go bytes.

use std::collections::HashMap;

// Go: patience.go:5 DiffType
/// The type of a diff element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiffType {
    /// A diff delete operation.
    Delete,
    /// A diff insert operation.
    Insert,
    /// No diff.
    Equal,
}

// Go: patience.go:17 DiffLine
/// A single line and its diff type.
// PORT: Go `Type` is `kind` (`type` is a Rust keyword).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DiffLine<'a> {
    pub text: &'a str,
    pub kind: DiffType,
}

// Go: patience.go:24 toDiffLines
/// Appends `a` as diff lines of type `t`.
// PORT: appends to `out` instead of returning a new slice.
fn to_diff_lines<'a>(out: &mut Vec<DiffLine<'a>>, a: &[&'a str], t: DiffType) {
    out.extend(a.iter().map(|&text| DiffLine { text, kind: t }));
}

// Go: patience.go:34 uniqueElements
/// Returns the elements that occur once in `a`, and their original indices.
fn unique_elements<'a>(a: &[&'a str]) -> (Vec<&'a str>, Vec<usize>) {
    let mut m: HashMap<&str, usize> = HashMap::new();
    for &e in a {
        *m.entry(e).or_insert(0) += 1;
    }
    let mut elements = Vec::new();
    let mut indices = Vec::new();
    for (i, &e) in a.iter().enumerate() {
        if m[e] == 1 {
            elements.push(e);
            indices.push(i);
        }
    }
    (elements, indices)
}

// Go: patience.go:51 Diff
/// Returns the patience diff of two slices of strings.
pub fn diff<'a>(a: &[&'a str], b: &[&'a str]) -> Vec<DiffLine<'a>> {
    let mut out = Vec::new();
    diff_into(&mut out, a, b);
    out
}

// PORT: Go `Diff` returns a new slice at each level and the caller appends
// it. This appends to `out` in the same order.
fn diff_into<'a>(out: &mut Vec<DiffLine<'a>>, a: &[&'a str], b: &[&'a str]) {
    if a.is_empty() && b.is_empty() {
        return;
    }
    if a.is_empty() {
        to_diff_lines(out, b, DiffType::Insert);
        return;
    }
    if b.is_empty() {
        to_diff_lines(out, a, DiffType::Delete);
        return;
    }

    // Find equal elements at the head of slices a and b.
    let mut i = 0;
    while i < a.len() && i < b.len() && a[i] == b[i] {
        i += 1;
    }
    if i > 0 {
        to_diff_lines(out, &a[..i], DiffType::Equal);
        diff_into(out, &a[i..], &b[i..]);
        return;
    }

    // Find equal elements at the tail of slices a and b.
    let mut j = 0;
    while j < a.len() && j < b.len() && a[a.len() - 1 - j] == b[b.len() - 1 - j] {
        j += 1;
    }
    if j > 0 {
        diff_into(out, &a[..a.len() - j], &b[..b.len() - j]);
        to_diff_lines(out, &a[a.len() - j..], DiffType::Equal);
        return;
    }

    // Find the longest common subsequence of unique elements in a and b.
    let (ua, idxa) = unique_elements(a);
    let (ub, idxb) = unique_elements(b);
    let mut lcs = lcs(&ua, &ub);

    // If the LCS is empty, the diff is all deletions and insertions.
    if lcs.is_empty() {
        to_diff_lines(out, a, DiffType::Delete);
        to_diff_lines(out, b, DiffType::Insert);
        return;
    }

    // Lookup the original indices of slices a and b.
    for x in &mut lcs {
        x[0] = idxa[x[0]];
        x[1] = idxb[x[1]];
    }

    let (mut ga, mut gb) = (0, 0);
    for ip in &lcs {
        // Diff the gaps between the lcs elements.
        diff_into(out, &a[ga..ip[0]], &b[gb..ip[1]]);
        // Append the LCS elements to the diff.
        out.push(DiffLine {
            kind: DiffType::Equal,
            text: a[ip[0]],
        });
        ga = ip[0] + 1;
        gb = ip[1] + 1;
    }
    // Diff the remaining elements of a and b after the final LCS element.
    diff_into(out, &a[ga..], &b[gb..]);
}

// Go: lcs.go:6 LCS
/// Computes the longest common subsequence of two string slices and returns
/// the index pairs of the LCS.
// PORT: the table is one `u32` vector instead of `[][]int`, to halve the
// memory of large tables. The values and the backtrack are the same.
pub fn lcs(a: &[&str], b: &[&str]) -> Vec<[usize; 2]> {
    // Initialize the LCS table.
    let width = b.len() + 1;
    let mut table = vec![0u32; (a.len() + 1) * width];
    let at = |i: usize, j: usize| i * width + j;

    // Populate the LCS table.
    for i in 1..=a.len() {
        for j in 1..=b.len() {
            table[at(i, j)] = if a[i - 1] == b[j - 1] {
                table[at(i - 1, j - 1)] + 1
            } else {
                table[at(i - 1, j)].max(table[at(i, j - 1)])
            };
        }
    }

    // Backtrack to find the LCS.
    let (mut i, mut j) = (a.len(), b.len());
    let mut s = Vec::with_capacity(table[at(i, j)] as usize);
    while i > 0 && j > 0 {
        if a[i - 1] == b[j - 1] {
            s.push([i - 1, j - 1]);
            i -= 1;
            j -= 1;
        } else if table[at(i - 1, j)] > table[at(i, j - 1)] {
            i -= 1;
        } else {
            j -= 1;
        }
    }

    // Reverse the backtracked LCS.
    s.reverse();
    s
}

// Go: unified.go:4 Hunk
/// A subsection of a diff.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hunk<'a> {
    pub diffs: Vec<DiffLine<'a>>,
    pub src_start: usize,
    pub src_lines: usize,
    pub dst_start: usize,
    pub dst_lines: usize,
}

// Go: unified.go:13 makeHunks (the updateHunks closure)
/// Updates `hunks` with a diff block.
// PORT: Go hunks share backing arrays with the blocks they come from. No
// block is read after it is passed here, so owned copies give the same
// hunks.
fn update_hunks<'a>(
    hunks: &mut Vec<Hunk<'a>>,
    block: &Hunk<'a>,
    last_block: bool,
    precontext: usize,
    postcontext: usize,
) {
    // PORT: Go `curHunk := len(hunks) - 1` is -1 when there are no hunks.
    // It is only read when there are hunks.
    let cur_hunk = hunks.len().wrapping_sub(1);
    if block.diffs[0].kind == DiffType::Equal {
        // Unmodified block.
        if hunks.is_empty() {
            // Start a new hunk with the tail of the block.
            let ctx_len = precontext.min(block.diffs.len());
            hunks.push(Hunk {
                diffs: block.diffs[block.diffs.len() - ctx_len..].to_vec(),
                src_start: block.diffs.len() - ctx_len + block.src_start,
                src_lines: ctx_len,
                dst_start: block.diffs.len() - ctx_len + block.dst_start,
                dst_lines: ctx_len,
            });
        } else {
            // Update the current hunk.
            let max_non_context = if last_block {
                postcontext
            } else {
                precontext + postcontext
            };
            if block.diffs.len() <= max_non_context {
                // Block is small enough to be appended to the current hunk.
                let hunk = &mut hunks[cur_hunk];
                hunk.diffs.extend_from_slice(&block.diffs);
                hunk.src_lines += block.diffs.len();
                hunk.dst_lines += block.diffs.len();
            } else {
                // Append the head of the block to the current hunk.
                let hunk = &mut hunks[cur_hunk];
                hunk.diffs.extend_from_slice(&block.diffs[..postcontext]);
                hunk.src_lines += postcontext;
                hunk.dst_lines += postcontext;
                if !last_block {
                    // Start a new hunk with the tail of the block.
                    hunks.push(Hunk {
                        diffs: block.diffs[block.diffs.len() - precontext..].to_vec(),
                        src_start: block.diffs.len() - precontext + block.src_start,
                        src_lines: precontext,
                        dst_start: block.diffs.len() - precontext + block.dst_start,
                        dst_lines: precontext,
                    });
                }
            }
            // Update starting line numbers if the current hunk had no source or destination diff.
            let hunk = &mut hunks[cur_hunk];
            if hunk.src_start == 0 {
                hunk.src_start = block.src_start;
            }
            if hunk.dst_start == 0 {
                hunk.dst_start = block.dst_start;
            }
        }
    } else {
        // Modified block.
        if hunks.is_empty() {
            hunks.push(Hunk {
                diffs: block.diffs.clone(),
                src_start: block.src_start,
                src_lines: block.src_lines,
                dst_start: block.dst_start,
                dst_lines: block.dst_lines,
            });
        } else {
            let hunk = &mut hunks[cur_hunk];
            hunk.diffs.extend_from_slice(&block.diffs);
            hunk.src_lines += block.src_lines;
            hunk.dst_lines += block.dst_lines;
        }
    }
}

// Go: unified.go:13 makeHunks
/// Returns the hunks of a diff.
pub fn make_hunks<'a>(
    diffs: &[DiffLine<'a>],
    precontext: usize,
    postcontext: usize,
) -> Vec<Hunk<'a>> {
    if diffs.is_empty() {
        return Vec::new();
    }

    let mut hunks: Vec<Hunk<'a>> = Vec::new();

    // Aggregate blocks of modified and unmodified diff lines, creating
    // or updating hunks after each block.
    let mut block = Hunk::default();
    let mut modified_lines = 0usize;
    let (mut src_line_num, mut dst_line_num) = (0usize, 0usize);
    for &l in diffs {
        if block.diffs.is_empty()
            || block.diffs[0].kind == l.kind
            || (block.diffs[0].kind != l.kind
                && block.diffs[0].kind != DiffType::Equal
                && l.kind != DiffType::Equal)
        {
            block.diffs.push(l);
        } else {
            update_hunks(&mut hunks, &block, false, precontext, postcontext);
            block = Hunk {
                diffs: vec![l],
                ..Hunk::default()
            };
        }

        match l.kind {
            DiffType::Delete => {
                src_line_num += 1;
                block.src_lines += 1;
                modified_lines += 1;
            }
            DiffType::Insert => {
                dst_line_num += 1;
                block.dst_lines += 1;
                modified_lines += 1;
            }
            DiffType::Equal => {
                src_line_num += 1;
                dst_line_num += 1;
                block.src_lines += 1;
                block.dst_lines += 1;
            }
        }

        if block.src_start == 0 && matches!(l.kind, DiffType::Equal | DiffType::Delete) {
            block.src_start = src_line_num;
        }
        if block.dst_start == 0 && matches!(l.kind, DiffType::Equal | DiffType::Insert) {
            block.dst_start = dst_line_num;
        }
    }
    update_hunks(&mut hunks, &block, true, precontext, postcontext);

    // Return no hunks if the diffs contain only equal lines.
    if modified_lines == 0 {
        return Vec::new();
    }

    hunks
}

// Go: format.go:10 typeSymbol
/// Returns the associated symbol of a `DiffType`.
fn type_symbol(t: DiffType) -> &'static str {
    match t {
        DiffType::Equal => " ",
        DiffType::Insert => "+",
        DiffType::Delete => "-",
    }
}

// Go: format.go:68 UnifiedDiffOptions
/// The options for `unified_diff_text_with_options`.
#[derive(Clone, Debug, Default)]
pub struct UnifiedDiffOptions {
    /// The number of lines of context before each change in a hunk.
    pub precontext: usize,
    /// The number of lines of context after each change in a hunk.
    pub postcontext: usize,
    /// The header for the source file.
    pub src_header: String,
    /// The header for the destination file.
    pub dst_header: String,
}

// Go: format.go:80 UnifiedDiffTextWithOptions
/// Returns the diff text in unidiff format.
pub fn unified_diff_text_with_options(diffs: &[DiffLine<'_>], opts: &UnifiedDiffOptions) -> String {
    let hunks = make_hunks(diffs, opts.precontext, opts.postcontext);
    let mut s: Vec<String> = Vec::new();
    if !opts.src_header.is_empty() {
        s.push(format!("--- {}", opts.src_header));
    }
    if !opts.dst_header.is_empty() {
        s.push(format!("+++ {}", opts.dst_header));
    }
    for h in &hunks {
        s.push(format!(
            "@@ -{},{} +{},{} @@",
            h.src_start, h.src_lines, h.dst_start, h.dst_lines
        ));
        for l in &h.diffs {
            if l.kind == DiffType::Equal && l.text.is_empty() {
                s.push(String::new());
            } else {
                s.push(format!("{}{}", type_symbol(l.kind), l.text));
            }
        }
    }
    s.join("\n")
}

// Go: format.go:103 UnifiedDiffText
/// Returns the diff text in unidiff format with a context of 3 lines.
pub fn unified_diff_text(diffs: &[DiffLine<'_>]) -> String {
    unified_diff_text_with_options(
        diffs,
        &UnifiedDiffOptions {
            precontext: 3,
            postcontext: 3,
            ..UnifiedDiffOptions::default()
        },
    )
}

// Go: stringutil/util.go:87 SplitLines
/// Splits `text` at `\r\n`, `\r` and `\n`. A final line break does not add
/// an empty line.
pub fn split_lines(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut lines = Vec::with_capacity(bytes.iter().filter(|&&b| b == b'\n').count() + 1);
    let mut start = 0;
    let mut pos = 0;
    while pos < bytes.len() {
        match bytes[pos] {
            b'\r' => {
                if pos + 1 < bytes.len() && bytes[pos + 1] == b'\n' {
                    lines.push(&text[start..pos]);
                    pos += 2;
                    start = pos;
                    continue;
                }
                // Go: fallthrough to '\n'.
                lines.push(&text[start..pos]);
                pos += 1;
                start = pos;
                continue;
            }
            b'\n' => {
                lines.push(&text[start..pos]);
                pos += 1;
                start = pos;
                continue;
            }
            _ => {}
        }
        pos += 1;
    }
    if start < bytes.len() {
        lines.push(&text[start..]);
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(text: &str, kind: DiffType) -> DiffLine<'_> {
        DiffLine { text, kind }
    }

    // Go: patience_test.go:9 Test_uniqueElements
    #[test]
    fn patience_unique_elements() {
        let unique = |a: &[&'static str]| unique_elements(a);
        assert_eq!(unique(&["a", "b", "c"]).0, vec!["a", "b", "c"]);
        assert_eq!(unique(&["a", "b", "c"]).1, vec![0usize, 1, 2]);
        assert_eq!(unique(&["a", "b", "a", "c"]).0, vec!["b", "c"]);
        assert_eq!(unique(&["a", "b", "a", "c"]).1, vec![1usize, 3]);
        assert!(unique(&["a", "b", "a", "c", "c", "b"]).0.is_empty());
        assert!(unique(&["a", "b", "a", "c", "c", "b"]).1.is_empty());
    }

    // Go: patience_test.go:57 TestDiff
    #[test]
    fn patience_diff() {
        use DiffType::{Delete, Equal, Insert};
        assert!(diff(&[], &[]).is_empty());
        assert_eq!(diff(&[], &["a"]), vec![line("a", Insert)]);
        assert_eq!(diff(&["a"], &[]), vec![line("a", Delete)]);
        assert_eq!(diff(&["a"], &["a"]), vec![line("a", Equal)]);
        assert_eq!(
            diff(&["a", "b"], &["a", "c"]),
            vec![line("a", Equal), line("b", Delete), line("c", Insert)]
        );
        assert_eq!(
            diff(&["a", "c"], &["b", "c"]),
            vec![line("a", Delete), line("b", Insert), line("c", Equal)]
        );
        assert_eq!(
            diff(&["a", "b", "c"], &["a", "d", "c"]),
            vec![
                line("a", Equal),
                line("b", Delete),
                line("d", Insert),
                line("c", Equal)
            ]
        );
        assert_eq!(
            diff(&["a", "w", "b", "x", "c"], &["a", "y", "b", "z", "c"]),
            vec![
                line("a", Equal),
                line("w", Delete),
                line("y", Insert),
                line("b", Equal),
                line("x", Delete),
                line("z", Insert),
                line("c", Equal)
            ]
        );
    }

    // Go: format_test.go:157 TestUnifiedDiffTextWithOptions
    #[test]
    fn patience_unified_diff_text_with_options() {
        use DiffType::{Delete, Equal, Insert};
        let diffs = [
            line("a", Equal),
            line("b", Equal),
            line("c", Insert),
            line("d", Equal),
            line("e", Equal),
            line("f", Equal),
            line("g", Delete),
            line("h", Insert),
            line("i", Equal),
            line("j", Insert),
            line("k", Equal),
            line("l", Equal),
        ];
        let opts = UnifiedDiffOptions {
            precontext: 1,
            postcontext: 1,
            ..UnifiedDiffOptions::default()
        };
        assert_eq!(
            unified_diff_text_with_options(&diffs, &opts),
            "@@ -2,2 +2,3 @@\n b\n+c\n d\n@@ -5,4 +6,5 @@\n f\n-g\n+h\n i\n+j\n k"
        );

        let diffs = [
            line("a", Equal),
            line("b", Equal),
            line("c", Insert),
            line("", Equal),
        ];
        let opts = UnifiedDiffOptions {
            precontext: 1,
            postcontext: 1,
            src_header: "a.txt".to_string(),
            dst_header: "b.txt".to_string(),
        };
        assert_eq!(
            unified_diff_text_with_options(&diffs, &opts),
            "--- a.txt\n+++ b.txt\n@@ -2,2 +2,3 @@\n b\n+c\n"
        );
    }

    #[test]
    fn stringutil_split_lines() {
        assert_eq!(split_lines(""), Vec::<&str>::new());
        assert_eq!(split_lines("a"), vec!["a"]);
        assert_eq!(split_lines("a\n"), vec!["a"]);
        assert_eq!(split_lines("a\r\nb\rc\n\nd"), vec!["a", "b", "c", "", "d"]);
        assert_eq!(split_lines("\r\r\n"), vec!["", ""]);
    }
}
