//! Go positions for the ts_ast tree.
//!
//! The Rust parser gives each node the range from its first token start to
//! its end. Go gives the full start: `pos` includes the leading trivia and is
//! the end of the previous token. Go list ranges also differ: a delimited
//! list starts just after its opener and ends at the full start of its closer.
//!
//! `TriviaRuns` records the maximal trivia runs of one file (white space,
//! line breaks, comments and the shebang). With it, the Rust ranges map to Go
//! ranges without a second parse.
//!
//! Go: scanner/scanner.go Scan (trivia skipping), parser/parser.go nodePos,
//! finishNode and parseDelimitedList.

use ts_ast::{NodeArena, NodeData, SyntaxKind};

/// The sorted, disjoint trivia runs `[start, end)` of one file.
#[derive(Default)]
pub struct TriviaRuns {
    starts: Vec<u32>,
    ends: Vec<u32>,
}

impl TriviaRuns {
    /// Scans `text` once. Literal tokens (strings, templates, regular
    /// expressions and JSX text) are opaque, because they can contain text
    /// that looks like a comment.
    #[must_use]
    pub fn compute(arena: &NodeArena, text: &str) -> Self {
        let mut opaque: Vec<(usize, usize)> = arena
            .iter()
            .filter(|(_, n)| is_opaque_token(n.kind))
            .map(|(_, n)| (n.range.start.get() as usize, n.range.end.get() as usize))
            .filter(|(s, e)| s < e)
            .collect();
        opaque.sort_unstable();

        let bytes = text.as_bytes();
        let mut runs = Self::default();
        let mut next_opaque = 0;
        let mut i = 0;
        if text.starts_with("#!") {
            i = line_end(bytes, 0);
        }
        let mut run_start = if i > 0 { Some(0) } else { None };
        while i < bytes.len() {
            while next_opaque < opaque.len() && opaque[next_opaque].0 < i {
                next_opaque += 1;
            }
            let limit = opaque.get(next_opaque).map_or(bytes.len(), |o| o.0);
            if i == limit {
                runs.close(&mut run_start, i);
                i = opaque[next_opaque].1.max(i + 1);
                continue;
            }
            let step = trivia_len(text, i, limit);
            if step > 0 {
                run_start.get_or_insert(i);
                i += step;
            } else {
                runs.close(&mut run_start, i);
                i += text[i..].chars().next().map_or(1, char::len_utf8);
            }
        }
        runs.close(&mut run_start, bytes.len());
        runs
    }

    fn close(&mut self, run_start: &mut Option<usize>, end: usize) {
        if let Some(start) = run_start.take() {
            self.starts.push(start as u32);
            self.ends.push(end as u32);
        }
    }

    /// The start of the trivia run that ends at `x`, else `x`. For a token
    /// start this is the Go full start of the token.
    #[must_use]
    pub fn full_start(&self, x: u32) -> u32 {
        match self.ends.binary_search(&x) {
            Ok(i) => self.starts[i],
            Err(_) => x,
        }
    }

    /// The end of the trivia run that starts at `x`, else `x`. For a token
    /// end this is the start of the next token.
    #[must_use]
    pub fn skip_from(&self, x: u32) -> u32 {
        match self.starts.binary_search(&x) {
            Ok(i) => self.ends[i],
            Err(_) => x,
        }
    }
}

/// Tokens whose text the trivia scan must not enter.
fn is_opaque_token(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateHead
            | SyntaxKind::TemplateMiddle
            | SyntaxKind::TemplateTail
            | SyntaxKind::RegularExpressionLiteral
            | SyntaxKind::JsxText
            | SyntaxKind::JsxTextAllWhiteSpaces
    )
}

fn line_end(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && bytes[i] != b'\n' && bytes[i] != b'\r' {
        i += 1;
    }
    i
}

/// The length of the trivia item at `i` (one white space character or one
/// comment), or 0. Stops at `limit`.
// Go: scanner/scanner.go Scan (the white space and comment cases)
fn trivia_len(text: &str, i: usize, limit: usize) -> usize {
    let bytes = text.as_bytes();
    match bytes[i] {
        b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c => 1,
        b'/' if i + 1 < limit && bytes[i + 1] == b'/' => line_end(bytes, i).min(limit) - i,
        b'/' if i + 1 < limit && bytes[i + 1] == b'*' => {
            let end = text[i + 2..].find("*/").map_or(bytes.len(), |p| i + 2 + p + 2);
            end.min(limit) - i
        }
        b if b < 0x80 => 0,
        _ => match text[i..].chars().next() {
            Some(c) if is_unicode_trivia(c) => c.len_utf8(),
            _ => 0,
        },
    }
}

// Go: stringutil.IsWhiteSpaceSingleLine and IsLineBreak (non-ASCII part)
fn is_unicode_trivia(c: char) -> bool {
    matches!(
        c,
        '\u{0085}'
            | '\u{00A0}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200B}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202F}'
            | '\u{205F}'
            | '\u{3000}'
            | '\u{FEFF}'
    )
}

/// The Go range of a list, from its Rust range, the Go ranges of its first
/// and last elements and the file text.
// Go: parser/parser.go parseDelimitedList, parseList and newNodeList. A
// delimited list starts after its opener. It ends after its last element,
// or after the trailing comma.
#[must_use]
pub fn go_list_range(runs: &TriviaRuns, text: &[u8], range: (u32, u32), elements: Option<((u32, u32), (u32, u32))>) -> (u32, u32) {
    let (s, e) = range;
    let opener_at = |x: u32| matches!(text.get(x as usize), Some(b'(' | b'[' | b'{' | b'<'));
    match elements {
        None => {
            if s < e && opener_at(s) {
                (s + 1, runs.full_start(e - 1).max(s + 1))
            } else {
                let p = runs.full_start(s);
                (p, p)
            }
        }
        Some(((first_pos, _), (_, last_end))) => {
            let pos = if s < first_pos && opener_at(s) { s + 1 } else { runs.full_start(s).min(first_pos) };
            let next = runs.skip_from(last_end);
            let end = if next < e && text.get(next as usize) == Some(&b',') { next + 1 } else { last_end };
            (pos, end)
        }
    }
}

/// The Go range of a parsed node. `id` and `n` are the node, `arena` and
/// `text` its file.
// PORT: besides the full start, the Rust parser differs from Go here:
// - a VariableDeclarationList in a VariableStatement starts at its first
//   declaration. Go starts it at the full start of the `var`/`let`/`const`
//   keyword (parser.go parseVariableDeclarationList).
// - a declaration without a body does not include its `;` (or `,` in a type).
//   Go does (parser.go parseFunctionBlockOrSemicolon, parseTypeMemberSemicolon).
// - an ImportType without a qualifier or type arguments and a DoStatement end
//   before their `)`. Go includes it (parser.go parseImportType,
//   parseDoStatement, which also takes an optional `;`).
// - a hole in an array binding pattern covers its comma. Go's BindingElement
//   there is zero-width.
#[must_use]
pub fn go_node_range(runs: &TriviaRuns, text: &[u8], arena: &NodeArena, n: &ts_ast::Node) -> (u32, u32) {
    let (s, e) = (n.range.start.get(), n.range.end.get());
    let parent = n.parent.and_then(|p| arena.get(p));
    let pos = match (&n.data, parent) {
        (NodeData::VariableDeclarationList(_), Some(p)) if p.kind == SyntaxKind::VariableStatement => {
            let last_modifier = match &p.data {
                NodeData::VariableStatement(d) => d.modifiers.as_ref().and_then(|m| m.list.nodes.last()).and_then(|&m| arena.get(m)),
                _ => None,
            };
            match last_modifier {
                Some(m) => m.range.end.get(),
                None => runs.full_start(p.range.start.get()),
            }
        }
        _ => runs.full_start(s),
    };
    let at = |x: u32| text.get(x as usize).copied();
    // The end after an optional `;` (or `,`) token that follows `e`.
    let absorb = |e: u32, allow_comma: bool| {
        if e > 0 && matches!(at(e - 1), Some(b';' | b',')) {
            return e;
        }
        let t = runs.skip_from(e);
        match at(t) {
            Some(b';') => t + 1,
            Some(b',') if allow_comma => t + 1,
            _ => e,
        }
    };
    let in_type = parent.is_some_and(|p| {
        matches!(p.kind, SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral | SyntaxKind::MappedType)
    });
    let end_of = |id: ts_ast::NodeId| arena.get(id).map_or(e, |c| c.range.end.get());
    // The end after the `)` that follows `x`, if there is one.
    let close_paren = |x: u32| {
        let t = runs.skip_from(x);
        if at(t) == Some(b')') { Some(t + 1) } else { None }
    };
    let end = match &n.data {
        NodeData::FunctionDeclaration(d) if d.body.is_none() => absorb(e, false),
        NodeData::MethodDeclaration(d) if d.body.is_none() => absorb(e, in_type),
        NodeData::ConstructorDeclaration(d) if d.body.is_none() => absorb(e, false),
        NodeData::GetAccessorDeclaration(d) if d.body.is_none() => absorb(e, in_type),
        NodeData::SetAccessorDeclaration(d) if d.body.is_none() => absorb(e, in_type),
        NodeData::PropertyDeclaration(_) if in_type => absorb(e, true),
        NodeData::MethodSignatureDeclaration(_)
        | NodeData::CallSignatureDeclaration(_)
        | NodeData::ConstructSignatureDeclaration(_)
        | NodeData::IndexSignatureDeclaration(_)
            if in_type =>
        {
            absorb(e, true)
        }
        NodeData::ImportTypeNode(d) if d.qualifier.is_none() && d.type_arguments.is_none() => {
            let last = d.attributes.map_or_else(|| end_of(d.argument), end_of);
            if last == e { close_paren(e).unwrap_or(e) } else { e }
        }
        // Go parseArrayBindingElement makes a zero-width BindingElement at
        // the comma of a hole. The Rust OmittedExpression covers the comma.
        NodeData::OmittedExpression(_) if parent.is_some_and(|p| p.kind == SyntaxKind::ArrayBindingPattern) => pos,
        NodeData::DoStatement(d) if end_of(d.expression) == e => match close_paren(e) {
            Some(x) => {
                let t = runs.skip_from(x);
                if at(t) == Some(b';') { t + 1 } else { x }
            }
            None => e,
        },
        _ => e,
    };
    (pos, end)
}
