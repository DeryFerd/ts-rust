#!/usr/bin/env python3
"""Edit-flow battery for the LSP parity oracle (goport tests2, sub-track S6 b2).

lsp_battery.py (int7) sends one open file and read-only requests. This script
writes goport-lsp-trace/1 traces for the flows it does not send:

  triggers   completion with trigger characters other than "." (quotes, "/",
             "@", "<", "#", " ", "`"); signatureHelp "<" and the ")" and
             content-change retriggers with activeSignatureHelp
  methods    linkedEditingRange, onTypeFormatting (";", "}", "\\n"),
             rangeFormatting, multiDocumentHighlight, sourceDefinition,
             _vs_references, willRenameFiles, custom/projectInfo
  edits      didChange (incremental ranges, several changes in one
             notification, whole-document text): insert, delete a line,
             break syntax then fix, type after "."
  fixes      error injection, then quickfix per diagnostic, quickfix with all
             diagnostics, source.fixAll, source.removeUnusedImports,
             source.sortImports, source.organizeImports, "source"
  prefs      didChangeConfiguration variants (quote style, module specifier,
             type-only imports, organize imports, format) before auto-import
             quickfixes, completion, organizeImports and formatting
  lifecycle  didSave, didClose, requests on the closed file, reopen
  inline     materialized projects: fs events with didChangeWatchedFiles
             (add, delete, rename, tsconfig.json, package.json,
             node_modules), watcher registration, isolatedDeclarations fixes,
             push diagnostics
  utf8       positionEncoding utf-8 on project files with non-ASCII text

Project roots are only read: edits are overlays (didChange), never disk
writes. fs events run only on materialized roots (lsp_oracle.py refuses them
on project roots).

Usage:
  lsp_battery_edits.py build --out TRACES [--parts b4-query-core,b4-inline,...]
  lsp_battery_edits.py list

build writes <TRACES>/<part>/<file>.jsonl and <TRACES>/b4.index.json. Run
them with the unchanged int7 lsp_oracle.py (`--battery b4`).

The lexer, the lsconv position math, Trace and the capabilities come from the
int7 lsp_battery.py, imported by path (LSP_BATTERY_PY overrides the path).
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path

REPO = Path("/home/theo/Code/sandbox/ts-rust")
INPUTS = REPO / "target/project-inputs"
LSP_BATTERY_PY = Path(os.environ.get(
    "LSP_BATTERY_PY", REPO / "target/worktrees/goport-int7/scripts/goport/lsp_battery.py"))


def load_lsp_battery(path: Path):
    spec = importlib.util.spec_from_file_location("lsp_battery", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


lb = load_lsp_battery(LSP_BATTERY_PY)

BATTERY = "b4"
RENAME_TO = "__goport_rename"
FORMAT_OPTIONS = {"tabSize": 2, "insertSpaces": True}
UTF8, UTF16 = lb.POSITION_ENCODING_KIND_UTF8, lb.POSITION_ENCODING_KIND_UTF16
# Go: lsproto FileChangeType
CREATED, CHANGED, DELETED = 1, 2, 3

PROJECTS = [
    {"name": "query-core", "root": INPUTS / "query/source/packages/query-core",
     "include": ["src/*"], "exclude": ["*/__tests__/*"], "expectFiles": 23},
    {"name": "hono", "root": INPUTS / "hono/source",
     "include": ["src/*"], "exclude": ["*.test.ts", "*.test.tsx"], "expectFiles": 188},
    {"name": "zod", "root": INPUTS / "zod/source/packages/zod",
     "include": ["src/*"], "exclude": ["*/tests/*", "*.test.ts"], "expectFiles": 131},
]

# didChangeConfiguration variants (Go: ls/lsutil/userpreferences.go and formatcodeoptions.go config paths).
PREF_VARIANTS = [
    {"preferences": {"quoteStyle": "single", "importModuleSpecifier": "relative",
                     "importModuleSpecifierEnding": "js"}},
    {"preferences": {"quoteStyle": "double", "importModuleSpecifier": "non-relative",
                     "importModuleSpecifierEnding": "minimal", "preferTypeOnlyAutoImports": True}},
    {"preferences": {"importModuleSpecifier": "project-relative", "importModuleSpecifierEnding": "index",
                     "organizeImports": {"caseSensitivity": "caseInsensitive", "unicodeCollation": "unicode",
                                         "typeOrder": "first"}},
     "format": {"semicolons": "remove", "insertSpaceAfterOpeningAndBeforeClosingNonemptyBraces": False}},
    {"suggest": {"autoImports": False, "includeCompletionsForImportStatements": False},
     "format": {"semicolons": "insert", "insertSpaceBeforeFunctionParenthesis": True,
                "placeOpenBraceOnNewLineForFunctions": True}},
]


def manifest() -> dict:
    return json.loads((lb.BATTERY_DIR / "b1.json").read_text())


# ---------------------------------------------------------------------------
# One open document
# ---------------------------------------------------------------------------


class Doc:
    """Text of one document, its version and the LSP position math for it."""

    def __init__(self, rel: str, text: bytes, encoding: str):
        self.rel, self.encoding = rel, encoding
        self.uri = lb.document_uri(rel)
        self.language_id = lb.LANGUAGE_IDS.get(os.path.splitext(rel)[1], "typescript")
        self.version = 1
        self.original = text
        self.set(text)

    def set(self, text: bytes):
        text.decode("utf-8")
        self.text = text
        line_map = lb.compute_lsp_line_starts(text)
        self.line_starts = line_map.line_starts
        self.conv = lb.new_converters(self.encoding, lambda _: line_map)
        self.script = lb.Script(self.rel, text)
        self.toks = lb.lex(text)

    def pos(self, offset: int) -> dict:
        return self.conv.position_to_line_and_character(self.script, offset)

    def rng(self, start: int, end: int) -> dict:
        return {"start": self.pos(start), "end": self.pos(end)}

    def full(self) -> dict:
        return self.rng(0, len(self.text))

    def td(self) -> dict:
        return {"textDocument": {"uri": self.uri}}

    def tdp(self, offset: int) -> dict:
        return {"textDocument": {"uri": self.uri}, "position": self.pos(offset)}

    def open(self, tr):
        self.version = 1
        tr.notification("textDocument/didOpen", {"textDocument": {
            "uri": self.uri, "languageId": self.language_id, "version": 1, "text": self.text.decode("utf-8")}})

    def change(self, tr, edits: list[tuple[int, int, bytes]]):
        """One didChange with incremental edits, applied in order. Offsets refer to the text
        after the earlier edits of the same list (LSP applies the changes one by one)."""
        changes = []
        for start, end, new in edits:
            rng = self.rng(start, end)
            # The server applies the range with LineAndCharacterToPosition; check it lands where we splice.
            assert self.conv.from_lsp_range(self.script, rng) == (start, end), (self.rel, start, end)
            changes.append({"range": rng, "text": new.decode("utf-8")})
            self.set(self.text[:start] + new + self.text[end:])
        self.version += 1
        tr.notification("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": self.version}, "contentChanges": changes})

    def replace_all(self, tr, new: bytes):
        self.version += 1
        tr.notification("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": self.version},
            "contentChanges": [{"text": new.decode("utf-8")}]})
        self.set(new)

    def names(self, start: int = 0) -> list:
        return [t for i, t in enumerate(self.toks) if t.start >= start and lb.is_name(self.toks, i)]

    def after_first_rune(self, offset: int) -> int:
        return offset + lb.decode_rune_in_string(self.text, offset)[1]


def initialize_params(encoding: str, push: bool = False, watch: bool = False) -> dict:
    m = manifest()
    caps = lb.get_capabilities_with_defaults(encoding)
    if watch:
        caps["workspace"]["didChangeWatchedFiles"] = {"dynamicRegistration": True, "relativePatternSupport": True}
    opts = dict(m["initializationOptions"])
    if push:
        opts["disablePushDiagnostics"] = False
    return {"processId": None, "rootUri": lb.ROOT_URI_PLACEHOLDER, "locale": "en-US",
            "capabilities": caps, "initializationOptions": opts}


def ata_off() -> dict:
    return manifest()["config"]["js/ts"]


def configure(tr, variant: dict | None):
    settings = json.loads(json.dumps(ata_off()))
    settings.update(variant or {})
    tr.notification("workspace/didChangeConfiguration", {"settings": {"js/ts": settings}})


spread = lb.spread  # all items, or `cap` items spaced evenly


# ---------------------------------------------------------------------------
# Anchors found with the int7 lexer
# ---------------------------------------------------------------------------


def depth_map(toks) -> list[int]:
    """Brace depth before each token."""
    out, depth = [], 0
    for t in toks:
        if t.kind == "}":
            depth = max(0, depth - 1)
        out.append(depth)
        if t.kind == "{":
            depth += 1
    return out


def import_statements(doc: Doc) -> list[dict]:
    """Top-level `import ... from "x"` statements: byte span, specifier token and the names in braces."""
    toks, depths, out = doc.toks, depth_map(doc.toks), []
    for i, t in enumerate(toks):
        if t.kind != "id" or t.text != "import" or depths[i] != 0:
            continue
        if i + 1 < len(toks) and toks[i + 1].kind in ("(", "."):
            continue
        j, names, braces = i + 1, [], False
        while j < len(toks) and toks[j].kind != "str" and toks[j].kind != ";":
            if toks[j].kind == "{":
                braces = True
            elif (braces and toks[j].kind == "id" and toks[j].text not in ("type", "as")
                  and not (j + 1 < len(toks) and toks[j + 1].text == "as")):
                names.append(toks[j].text)
            j += 1
        if j >= len(toks) or toks[j].kind != "str":
            continue
        end = toks[j].end
        if j + 1 < len(toks) and toks[j + 1].kind == ";":
            end = toks[j + 1].end
        out.append({"start": t.start, "end": end, "spec": toks[j], "names": names})
    return out


def module_strings(doc: Doc) -> list:
    """String tokens that name a module (import/export from, side-effect import, import(), require())."""
    toks, out = doc.toks, []
    for i, t in enumerate(toks):
        if t.kind != "str" or i == 0:
            continue
        p = toks[i - 1]
        if (p.kind == "id" and p.text in ("from", "import")) or (
                p.kind == "(" and i > 1 and toks[i - 2].text in ("import", "require")):
            out.append(t)
    return out


def interfaces(doc: Doc) -> list[tuple[str, int]]:
    """(name, type parameter count) of interfaces declared in the file."""
    toks, out = doc.toks, []
    for i in range(len(toks) - 1):
        if toks[i].text != "interface" or toks[i].kind != "id" or not lb.is_name(toks, i + 1):
            continue
        if i > 0 and toks[i - 1].kind in (".", "?."):
            continue
        count, j = 0, i + 2
        if j < len(toks) and toks[j].kind == "<":
            count, depth = 1, 0
            while j < len(toks):
                k = toks[j].kind
                depth += (k == "<") - (k == ">")
                if depth == 1 and k == ",":
                    count += 1
                if depth == 0:
                    break
                j += 1
        out.append((toks[i + 1].text, count))
    return out


DECL_KEYWORDS = {"const": "value", "let": "value", "var": "value", "function": "value", "class": "value",
                 "enum": "value", "interface": "type", "type": "type"}


def exported_names(doc: Doc) -> list[tuple[str, str]]:
    """(name, "value" | "type") of non-generic top-level `export <decl> Name` declarations."""
    toks, depths, out = doc.toks, depth_map(doc.toks), []
    for i, t in enumerate(toks):
        if t.text != "export" or t.kind != "id" or depths[i] != 0:
            continue
        j = i + 1
        while j < len(toks) and toks[j].text in ("declare", "abstract", "async"):
            j += 1
        if j >= len(toks) or toks[j].text not in DECL_KEYWORDS:
            continue
        kind = DECL_KEYWORDS[toks[j].text]
        j += 1
        if j < len(toks) and toks[j].kind == "*":
            j += 1
        if j + 1 < len(toks) and toks[j].kind == "id" and toks[j + 1].kind != "<" and len(toks[j].text) >= 4:
            out.append((toks[j].text, kind))
    return out


def calls(doc: Doc) -> list[tuple[int, int]]:
    """(open paren index, close paren index) of call-like parens after a name."""
    match = lb.match_brackets(doc.toks)
    return [(i, match[i]) for i, t in enumerate(doc.toks)
            if t.kind == "(" and i > 0 and lb.is_name(doc.toks, i - 1) and i in match]


def line_of(doc: Doc, offset: int) -> int:
    return doc.pos(offset)["line"]


def line_span(doc: Doc, line: int) -> tuple[int, int]:
    starts = doc.line_starts
    return starts[line], starts[line + 1] if line + 1 < len(starts) else len(doc.text)


# ---------------------------------------------------------------------------
# Flows. Each flow leaves the document as it found it.
# ---------------------------------------------------------------------------


def completion(tr, doc: Doc, offset: int, trigger: str | None = None, kind: int | None = None, resolve: int = 1):
    ctx = {"triggerKind": kind or (2 if trigger else 1)}
    if trigger:
        ctx["triggerCharacter"] = trigger
    ev = tr.request("textDocument/completion", {**doc.tdp(offset), "context": ctx})
    for i in range(resolve):
        tr.request("completionItem/resolve", params_from={
            "event": ev, "pointer": "/items", "pick": {"sortBy": ["sortText", "label"], "index": i}})
    return ev


def flow_triggers(tr, doc: Doc):
    toks, text = doc.toks, doc.text
    specs = module_strings(doc)
    for t in spread(specs, 2):
        completion(tr, doc, t.start + 1, t.text[:1])
    slashes = [(t.start + t.text.rfind("/") + 1) for t in specs if "/" in t.text[1:-1]]
    for at in spread(slashes, 2):
        completion(tr, doc, at, "/")
    args = [t for i, t in enumerate(toks) if t.kind == "str" and t not in specs and i > 0
            and toks[i - 1].kind in ("(", ",")]
    for t in spread(args, 2):
        completion(tr, doc, t.start + 1, t.text[:1])
    ats = [block.start() + m.start() + 1 for block in re.finditer(rb"/\*\*.*?\*/", text, re.DOTALL)
           for m in re.finditer(rb"@[a-zA-Z]", block.group(0))]
    for at in spread(ats, 2):
        completion(tr, doc, at, "@")
    lts = [t.end for i, t in enumerate(toks) if t.kind == "<" and i > 0 and lb.is_name(toks, i - 1)]
    for at in spread(lts, 2):
        completion(tr, doc, at, "<")
    for t in spread([t for t in toks if t.kind == "priv"], 1):
        completion(tr, doc, t.start + 1, "#")
    spaces = [t.end + 1 for i, t in enumerate(toks) if t.kind == "id" and t.text in ("import", "new", "extends")
              and text[t.end:t.end + 1] == b" " and not (i > 0 and toks[i - 1].kind in (".", "?."))]
    for at in spread(spaces, 2):
        completion(tr, doc, at, " ")
    for t in spread([t for t in toks if t.kind == "tmpl" and t.text.startswith("`")], 1):
        completion(tr, doc, t.start + 1, "`")


def signature_help(tr, doc: Doc, offset: int, trigger: str | None, kind: int, retrigger=False, from_event=None):
    ctx = {"triggerKind": kind, "isRetrigger": retrigger}
    if trigger:
        ctx["triggerCharacter"] = trigger
    pf = None
    if from_event is not None:
        pf = {"event": from_event, "pointer": "", "into": "/context/activeSignatureHelp"}
    return tr.request("textDocument/signatureHelp", {**doc.tdp(offset), "context": ctx}, pf)


def flow_signature(tr, doc: Doc):
    toks = doc.toks
    lts = [t.end for i, t in enumerate(toks) if t.kind == "<" and i > 0 and lb.is_name(toks, i - 1)]
    for at in spread(lts, 2):
        signature_help(tr, doc, at, "<", 2)
    # A call with a nested call: open the outer help, then ")" after the inner call and a
    # content-change retrigger at the first comma, both with activeSignatureHelp.
    all_calls = calls(doc)
    nested = []
    for open_i, close_i in all_calls:
        inner = [c for c in all_calls if open_i < c[0] and c[1] < close_i]
        if inner:
            nested.append((open_i, close_i, inner[0]))
    for open_i, close_i, (_, inner_close) in spread(nested, 3):
        first = signature_help(tr, doc, toks[open_i].end, "(", 2)
        signature_help(tr, doc, toks[inner_close].end, ")", 2, True, first)
        comma = next((j for j in range(inner_close, close_i) if toks[j].kind == ","), None)
        if comma is not None:
            signature_help(tr, doc, toks[comma].end, None, 3, True, first)


def flow_methods(tr, doc: Doc):
    toks, text = doc.toks, doc.text
    names = doc.names()
    picks = spread(names, 3)
    # linkedEditingRange: JSX tag names in .tsx files, else plain identifiers (null answers).
    tags = [toks[i + 1] for i in range(len(toks) - 1) if toks[i].kind == "<" and toks[i + 1].kind == "id"
            and (i == 0 or not lb.is_name(toks, i - 1))]
    for t in spread(tags, 3) if doc.rel.endswith((".tsx", ".jsx")) else picks[:1]:
        tr.request("textDocument/linkedEditingRange", doc.tdp(doc.after_first_rune(t.start)))
    for kind, ch in ((";", ";"), ("}", "}")):
        for t in spread([t for t in toks if t.kind == kind], 2):
            tr.request("textDocument/onTypeFormatting", {**doc.tdp(t.end), "ch": ch, "options": FORMAT_OPTIONS})
    brace_lines = [n + 1 for n in range(len(doc.line_starts) - 1)
                   if text[slice(*line_span(doc, n))].rstrip().endswith(b"{")]
    for n in spread(brace_lines, 2):
        tr.request("textDocument/onTypeFormatting", {
            "textDocument": {"uri": doc.uri}, "position": {"line": n, "character": 0}, "ch": "\n",
            "options": FORMAT_OPTIONS})
    last = min(20, len(doc.line_starts) - 1)
    tr.request("textDocument/rangeFormatting", {**doc.td(), "range": {
        "start": {"line": 0, "character": 0}, "end": {"line": last, "character": 0}}, "options": FORMAT_OPTIONS})
    match = lb.match_brackets(toks)
    blocks = [(toks[i].start, toks[match[i]].end) for i in range(len(toks))
              if toks[i].kind == "{" and i in match and line_of(doc, toks[match[i]].start) - line_of(doc, toks[i].start) >= 3]
    for start, end in spread(blocks, 1):
        tr.request("textDocument/rangeFormatting", {**doc.td(), "range": doc.rng(start, end), "options": FORMAT_OPTIONS})
    for t in picks[:2]:
        tr.request("custom/textDocument/multiDocumentHighlight", {
            **doc.tdp(doc.after_first_rune(t.start)), "filesToSearch": [doc.uri]})
    imported = [t for st in import_statements(doc) for t in names
                if st["start"] <= t.start and t.end <= st["end"] and t.text in st["names"]]
    for t in spread(imported, 2) + picks[1:2]:
        tr.request("custom/textDocument/sourceDefinition", doc.tdp(doc.after_first_rune(t.start)))
    for t in picks[:2]:
        tr.request("textDocument/_vs_references", {**doc.tdp(doc.after_first_rune(t.start)),
                                                   "context": {"includeDeclaration": True}})
    base, ext = os.path.splitext(os.path.basename(doc.rel))
    parent = os.path.dirname(doc.rel)
    renamed = lb.document_uri(os.path.join(parent, f"{base}__goport_renamed{ext}"))
    tr.request("workspace/willRenameFiles", {"files": [{"oldUri": doc.uri, "newUri": renamed}]})
    if parent:
        tr.request("workspace/willRenameFiles", {"files": [{
            "oldUri": lb.document_uri(parent), "newUri": lb.document_uri(parent + "__goport_renamed")}]})
    tr.request("custom/projectInfo", doc.td())


def after_imports(doc: Doc) -> int:
    """Offset of the line start after the last top-level import (0 without imports)."""
    stmts = import_statements(doc)
    if not stmts:
        return 0
    line = line_of(doc, stmts[-1]["end"])
    return line_span(doc, line)[1]


def flow_edits(tr, doc: Doc):
    original = doc.text
    # 1. Insert a declaration after the imports.
    at = after_imports(doc)
    new = b"const __goport_edit = [1, 'a'] as const;\n"
    doc.change(tr, [(at, at, new)])
    tr.request("textDocument/diagnostic", doc.td())
    name_at = at + len(b"const ") + 1
    tr.request("textDocument/hover", doc.tdp(name_at))
    tr.request("textDocument/documentHighlight", doc.tdp(name_at))
    later = [t for t in doc.names(at + len(new))]
    if later:
        completion(tr, doc, later[len(later) // 2].start, resolve=0)
    tr.request("textDocument/semanticTokens/full", doc.td())
    doc.change(tr, [(at, at + len(new), b"")])

    # 2. Delete a non-empty line near 60% of the file, then put it back.
    lines = [n for n in range(len(doc.line_starts)) if doc.text[slice(*line_span(doc, n))].strip()
             and not doc.text[slice(*line_span(doc, n))].lstrip().startswith(b"import")]
    if lines:
        n = lines[len(lines) * 3 // 5]
        start, end = line_span(doc, n)
        removed = doc.text[start:end]
        doc.change(tr, [(start, end, b"")])
        tr.request("textDocument/diagnostic", doc.td())
        tr.request("textDocument/documentSymbol", doc.td())
        tr.request("textDocument/foldingRange", doc.td())
        tr.request("textDocument/semanticTokens/full", doc.td())
        after = doc.names(start)
        if after:
            tr.request("textDocument/hover", doc.tdp(doc.after_first_rune(after[0].start)))
        doc.change(tr, [(start, start, removed)])

    # 3. Break the syntax at a block start near 40% of the file, then fix it.
    opens = [t for t in doc.toks if t.kind == "{"]
    if opens:
        t = opens[len(opens) * 2 // 5]
        junk = b" if ( "
        doc.change(tr, [(t.end, t.end, junk)])
        tr.request("textDocument/diagnostic", doc.td())
        tr.request("textDocument/documentSymbol", doc.td())
        tr.request("textDocument/foldingRange", doc.td())
        tr.request("textDocument/semanticTokens/full", doc.td())
        after = doc.names(t.end + len(junk))
        if after:
            tr.request("textDocument/selectionRange", {**doc.td(), "positions": [doc.pos(after[0].start)]})
            tr.request("textDocument/hover", doc.tdp(doc.after_first_rune(after[0].start)))
            completion(tr, doc, after[0].start, resolve=0)
        doc.change(tr, [(t.end, t.end + len(junk), b"")])
        tr.request("textDocument/diagnostic", doc.td())

    # 4. Type after "." at the end of the file, one character at a time.
    dots = [i for i, t in enumerate(doc.toks) if t.kind == "." and i > 0 and doc.toks[i - 1].kind == "id"
            and i + 1 < len(doc.toks) and doc.toks[i + 1].kind == "id"]
    if dots:
        i = dots[len(dots) // 2]
        receiver, member = doc.toks[i - 1].text.encode(), doc.toks[i + 1].text.encode()
        end = len(doc.text)
        head = b"\n" + receiver + b"."
        doc.change(tr, [(end, end, head)])
        completion(tr, doc, len(doc.text), ".")
        doc.change(tr, [(len(doc.text), len(doc.text), member[:1])])
        completion(tr, doc, len(doc.text), kind=3)
        tr.request("textDocument/signatureHelp", {**doc.tdp(len(doc.text)),
                                                  "context": {"triggerKind": 1, "isRetrigger": False}})
        doc.replace_all(tr, original)

    # 5. Two changes in one notification, then a whole-document replace back.
    head, tail = b"/* goport a */\n", b"\n// goport b\n"
    end = len(original) + len(head)  # the second range is on the text after the first change
    doc.change(tr, [(0, 0, head), (end, end, tail)])
    tr.request("textDocument/foldingRange", doc.td())
    tr.request("textDocument/semanticTokens/full", doc.td())
    tr.request("textDocument/diagnostic", doc.td())
    doc.replace_all(tr, original)
    tr.request("textDocument/diagnostic", doc.td())


def quickfixes(tr, doc: Doc, diagnostic: int, cap: int):
    for i in range(cap):
        tr.request("textDocument/codeAction",
                   {**doc.td(), "range": None,
                    "context": {"diagnostics": [None], "only": ["quickfix"], "triggerKind": 1}},
                   {"event": diagnostic, "pointer": "/items", "pick": {"index": i},
                    "into": [{"to": "/range", "from": "/range"}, {"to": "/context/diagnostics/0", "from": ""}]})


def source_action(tr, doc: Doc, only: list[str] | None, rng: dict | None = None):
    ctx = {"diagnostics": [], "triggerKind": 1}
    if only is not None:
        ctx["only"] = only
    zero = {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}}
    return tr.request("textDocument/codeAction", {**doc.td(), "range": rng or zero, "context": ctx})


def all_diagnostics_action(tr, doc: Doc, diagnostic: int):
    tr.request("textDocument/codeAction",
               {**doc.td(), "range": doc.full(), "context": {"diagnostics": [], "triggerKind": 1}},
               {"event": diagnostic, "pointer": "/items", "into": "/context/diagnostics"})


def pick_missing_export(doc: Doc, exports: dict) -> tuple[str, str] | None:
    """A name that another project file exports and this file never mentions."""
    present = {t.text for t in doc.toks if t.kind == "id"}
    cands = sorted({(n, k) for rel, names in exports.items() if rel != doc.rel for n, k in names
                    if n not in present})
    if not cands:
        return None
    return cands[int(hashlib.sha256(doc.rel.encode()).hexdigest(), 16) % len(cands)]


def flow_fixes(tr, doc: Doc, exports: dict):
    original = doc.text
    source_action(tr, doc, ["source.sortImports"])
    source_action(tr, doc, ["source.removeUnusedImports"])

    stmts = import_statements(doc)
    named = [s for s in stmts if s["names"]]
    if named:
        # 1. Remove an import: "Cannot find name" diagnostics and auto-import fixes.
        s = named[0]
        removed = doc.text[s["start"]:s["end"]]
        doc.change(tr, [(s["start"], s["end"], b"")])
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfixes(tr, doc, d, 6)
        all_diagnostics_action(tr, doc, d)
        source_action(tr, doc, ["source.fixAll"])
        source_action(tr, doc, ["source"])
        doc.change(tr, [(s["start"], s["start"], removed)])

        # 2. An unused duplicate import at the top.
        spec = s["spec"].text.encode()
        dup = b"import { " + s["names"][0].encode() + b" as __goport_unused } from " + spec + b";\n"
        doc.change(tr, [(0, 0, dup)])
        tr.request("textDocument/diagnostic", doc.td())
        for kind in ("source.removeUnusedImports", "source.sortImports", "source.organizeImports"):
            source_action(tr, doc, [kind])
        doc.change(tr, [(0, len(dup), b"")])

    # 3. A class that does not implement an interface of this file.
    ifaces = interfaces(doc)
    if ifaces:
        name, count = ifaces[0]
        args = b"<" + b", ".join([b"any"] * count) + b">" if count else b""
        cls = b"\nclass __GoportImpl implements " + name.encode() + args + b" {}\n"
        end = len(doc.text)
        doc.change(tr, [(end, end, cls)])
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfixes(tr, doc, d, 3)
        source_action(tr, doc, ["source.fixAll"])
        doc.change(tr, [(end, end + len(cls), b"")])

    # 4. A misspelled member: "Did you mean" diagnostics (Go has no spelling fix).
    dots = [i for i, t in enumerate(doc.toks) if t.kind == "." and i + 1 < len(doc.toks)
            and doc.toks[i + 1].kind == "id" and len(doc.toks[i + 1].text) >= 3]
    if dots:
        t = doc.toks[dots[len(dots) // 2] + 1]
        doc.change(tr, [(t.end, t.end, t.text[-1:].encode())])
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfixes(tr, doc, d, 2)
        doc.change(tr, [(t.end, t.end + 1, b"")])

    # 5. A name exported by another file: auto-import fixes under preference variants.
    missing = pick_missing_export(doc, exports)
    if missing:
        name, kind = missing
        line = (b"\nvoid " + name.encode() + b";\n") if kind == "value" \
            else (b"\ntype __GoportFix = " + name.encode() + b";\n")
        end = len(doc.text)
        doc.change(tr, [(end, end, line)])
        name_at = end + line.index(name.encode())
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfixes(tr, doc, d, 3)
        source_action(tr, doc, ["source.fixAll"])
        for variant in PREF_VARIANTS:
            configure(tr, variant)
            tr.request("textDocument/codeAction",
                       {**doc.td(), "range": None,
                        "context": {"diagnostics": [None], "only": ["quickfix"], "triggerKind": 1}},
                       {"event": d, "pointer": "/items", "pick": {"match": {"code": 2304}},
                        "into": [{"to": "/range", "from": "/range"}, {"to": "/context/diagnostics/0", "from": ""}]})
            completion(tr, doc, name_at + 1, resolve=2)
            source_action(tr, doc, ["source.organizeImports"])
            tr.request("textDocument/formatting", {**doc.td(), "options": FORMAT_OPTIONS})
        configure(tr, None)
        doc.change(tr, [(end, end + len(line), b"")])
    assert doc.text == original


def flow_lifecycle(tr, doc: Doc):
    original = doc.text
    names = doc.names()
    doc.change(tr, [(0, 0, b"// goport dirty\n")])
    tr.notification("textDocument/didSave", doc.td())
    tr.request("textDocument/diagnostic", doc.td())
    doc.replace_all(tr, original)
    tr.notification("textDocument/didClose", doc.td())
    probe = names[len(names) // 3] if names else None
    if probe is not None:
        tr.request("textDocument/hover", doc.tdp(doc.after_first_rune(probe.start)))
        tr.request("textDocument/definition", doc.tdp(doc.after_first_rune(probe.start)))
    tr.request("textDocument/documentSymbol", doc.td())
    tr.request("custom/projectInfo", doc.td())
    doc.open(tr)
    tr.request("textDocument/diagnostic", doc.td())
    if probe is not None:
        tr.request("textDocument/hover", doc.tdp(doc.after_first_rune(probe.start)))


def flow_utf8(tr, doc: Doc):
    """Requests at identifiers on lines with non-ASCII text, then a non-ASCII edit."""
    wide = {n for n in range(len(doc.line_starts)) if any(b >= 0x80 for b in doc.text[slice(*line_span(doc, n))])}
    names = [t for t in doc.names() if line_of(doc, t.start) in wide]
    for t in spread(names or doc.names(), 12):
        tdp = doc.tdp(doc.after_first_rune(t.start))
        tr.request("textDocument/hover", tdp)
        tr.request("textDocument/definition", tdp)
        tr.request("textDocument/references", {**tdp, "context": {"includeDeclaration": True}})
        tr.request("textDocument/documentHighlight", tdp)
        tr.request("textDocument/rename", {**tdp, "newName": RENAME_TO})
        tr.request("textDocument/selectionRange", {**doc.td(), "positions": [tdp["position"]]})
    strs = [t for t in doc.toks if t.kind in ("str", "tmpl") and line_of(doc, t.start) in wide]
    for t in spread(strs, 3):
        completion(tr, doc, t.end - 1, resolve=0)
    for method in ("textDocument/diagnostic", "textDocument/documentSymbol", "textDocument/foldingRange",
                   "textDocument/semanticTokens/full"):
        tr.request(method, doc.td())
    tr.request("textDocument/inlayHint", {**doc.td(), "range": doc.full()})
    tr.request("textDocument/formatting", {**doc.td(), "options": FORMAT_OPTIONS})
    original = doc.text
    at = after_imports(doc)
    new = "const __goport_ütf = 'ä😀€';\n".encode()
    doc.change(tr, [(at, at, new)])
    tr.request("textDocument/hover", doc.tdp(at + len(b"const ") + 1))
    tr.request("textDocument/diagnostic", doc.td())
    tr.request("textDocument/semanticTokens/full", doc.td())
    later = doc.names(at + len(new))
    if later:
        tr.request("textDocument/hover", doc.tdp(doc.after_first_rune(later[0].start)))
    doc.change(tr, [(at, at + len(new), b"")])
    assert doc.text == original


# ---------------------------------------------------------------------------
# Project parts
# ---------------------------------------------------------------------------


def header(name: str, source: dict, root: dict, encoding: str) -> dict:
    return {"format": lb.TRACE_FORMAT, "name": name, "source": source, "root": root, "cwd": "",
            "config": manifest()["config"], "positionEncoding": encoding}


def project_sources(project: dict) -> list[str]:
    rels = lb.list_sources(project["root"], project["include"], project["exclude"], manifest()["sweep"]["extensions"])
    if len(rels) != project["expectFiles"]:
        raise SystemExit(f"{project['name']}: found {len(rels)} files, expected {project['expectFiles']}")
    return rels


def project_part(project: dict, out_dir: Path) -> list[dict]:
    root = project["root"]
    rels = project_sources(project)
    texts = {rel: lb.read_source(root / rel) for rel in rels}
    exports = {rel: exported_names(Doc(rel, text, UTF16)) for rel, text in texts.items()}
    entries = []
    for rel in rels:
        text = texts[rel]
        tr = lb.Trace()
        tr.request("initialize", initialize_params(UTF16))
        doc = Doc(rel, text, UTF16)
        doc.open(tr)
        for flow in (flow_triggers, flow_signature, flow_methods, flow_edits):
            flow(tr, doc)
        flow_fixes(tr, doc, exports)
        flow_lifecycle(tr, doc)
        name = f"{BATTERY}-{project['name']}/{rel}"
        src = {"kind": "edits", "part": f"{BATTERY}-{project['name']}", "file": rel, "complete": True,
               "sha256": hashlib.sha256(text).hexdigest()}
        entries.append(lb.write_trace(out_dir, header(name, src, {"kind": "project", "dir": str(root.resolve())},
                                                      UTF16), tr))
    return entries


def utf8_part(out_dir: Path) -> list[dict]:
    entries = []
    for project in PROJECTS:
        root = project["root"]
        for rel in project_sources(project):
            text = lb.read_source(root / rel)
            if all(b < 0x80 for b in text):
                continue
            tr = lb.Trace()
            tr.request("initialize", initialize_params(UTF8))
            doc = Doc(rel, text, UTF8)
            doc.open(tr)
            flow_utf8(tr, doc)
            name = f"{BATTERY}-utf8/{project['name']}/{rel}"
            src = {"kind": "utf8", "part": f"{BATTERY}-utf8", "project": project["name"], "file": rel,
                   "complete": True, "sha256": hashlib.sha256(text).hexdigest()}
            entries.append(lb.write_trace(out_dir, header(name, src, {"kind": "project", "dir": str(root.resolve())},
                                                          UTF8), tr))
    return entries


# ---------------------------------------------------------------------------
# Inline (materialized) cases: fs events, watchers, isolatedDeclarations, push diagnostics
# ---------------------------------------------------------------------------


class Case:
    """One materialized project and its session."""

    def __init__(self, name: str, description: str, files: dict[str, str], push=False, watch=False):
        self.name, self.description, self.files = name, description, dict(files)
        self.disk = dict(files)
        self.tr = lb.Trace()
        self.tr.request("initialize", initialize_params(UTF16, push=push, watch=watch))
        self.docs: dict[str, Doc] = {}

    def open(self, rel: str) -> Doc:
        doc = Doc(rel, self.disk[rel].encode(), UTF16)
        doc.open(self.tr)
        self.docs[rel] = doc
        return doc

    def close(self, rel: str):
        self.tr.notification("textDocument/didClose", {"textDocument": {"uri": lb.document_uri(rel)}})
        self.docs.pop(rel, None)

    def write(self, rel: str, content: str, notify=True):
        kind = CHANGED if rel in self.disk else CREATED
        self.disk[rel] = content
        self.tr.events.append({"kind": "fs", "op": "write", "path": rel, "content": content})
        if notify:
            self.watched([(rel, kind)])

    def remove(self, rel: str, notify=True):
        self.disk.pop(rel)
        self.tr.events.append({"kind": "fs", "op": "remove", "path": rel})
        if notify:
            self.watched([(rel, DELETED)])

    def watched(self, changes: list[tuple[str, int]]):
        self.tr.notification("workspace/didChangeWatchedFiles", {
            "changes": [{"uri": lb.document_uri(rel), "type": kind} for rel, kind in changes]})

    def diag(self, doc: Doc) -> int:
        return self.tr.request("textDocument/diagnostic", doc.td())

    def at(self, doc: Doc, needle: str, occurrence: int = 1) -> int:
        at = -1
        for _ in range(occurrence):
            at = doc.text.index(needle.encode(), at + 1)
        return at

    def entry(self, out_dir: Path) -> dict:
        name = f"{BATTERY}-inline/{self.name}"
        src = {"kind": "inline", "part": f"{BATTERY}-inline", "case": self.name, "complete": True,
               "description": self.description}
        return lb.write_trace(out_dir, header(name, src, {"kind": "materialize", "files": self.files}, UTF16),
                              self.tr)


TSCONFIG = json.dumps({"compilerOptions": {"strict": True, "module": "nodenext", "target": "es2022"}}, indent=2)


def case_fs_add_delete_rename(watch: bool) -> Case:
    c = Case("fs-watch-register" if watch else "fs-add-delete-rename",
             "create, delete and rename an imported file with didChangeWatchedFiles"
             + (" (client supports watcher registration)" if watch else ""),
             {"tsconfig.json": TSCONFIG, "package.json": '{ "type": "module" }\n',
              "src/a.ts": 'import { b } from "./b.js";\nexport const a: number = b + 1;\n'}, watch=watch)
    a = c.open("src/a.ts")
    c.diag(a)
    c.write("src/b.ts", "export const b = 1;\n")
    c.diag(a)
    b_at = c.at(a, "b }")
    c.tr.request("textDocument/definition", a.tdp(b_at))
    c.tr.request("textDocument/hover", a.tdp(c.at(a, "b + 1")))
    c.remove("src/b.ts")
    c.diag(a)
    c.write("src/c.ts", 'export const b = "now a string";\n', notify=False)
    c.write("src/b.ts", 'export { b } from "./c.js";\n', notify=False)
    c.watched([("src/c.ts", CREATED), ("src/b.ts", CREATED)])
    c.diag(a)
    c.tr.request("textDocument/definition", a.tdp(b_at))
    c.tr.request("workspace/willRenameFiles", {"files": [{
        "oldUri": lb.document_uri("src/c.ts"), "newUri": lb.document_uri("src/lib/c2.ts")}]})
    c.remove("src/c.ts", notify=False)
    c.write("src/lib/c2.ts", 'export const b = "now a string";\n', notify=False)
    c.watched([("src/c.ts", DELETED), ("src/lib/c2.ts", CREATED)])
    c.diag(a)
    c.tr.request("textDocument/completion", {**a.tdp(len(a.text)), "context": {"triggerKind": 1}})
    return c


def case_fs_tsconfig() -> Case:
    loose = json.dumps({"compilerOptions": {"strict": False, "module": "esnext", "target": "es2022"}}, indent=2)
    c = Case("fs-tsconfig", "tsconfig.json changes: strict on, then a file leaves the include list",
             {"tsconfig.json": loose, "src/a.ts": "export function f(x) {\n  return x;\n}\nf(1);\n",
              "src/b.ts": "import { f } from './a';\nexport const y: string = f(2);\n"})
    a, b = c.open("src/a.ts"), c.open("src/b.ts")
    c.diag(a)
    c.diag(b)
    c.tr.request("custom/projectInfo", a.td())
    c.write("tsconfig.json", json.dumps({"compilerOptions": {"strict": True, "module": "esnext", "target": "es2022"}},
                                        indent=2))
    c.diag(a)
    c.diag(b)
    c.tr.request("textDocument/hover", b.tdp(c.at(b, "f(2)")))
    c.write("tsconfig.json", json.dumps({"compilerOptions": {"strict": True, "module": "esnext"},
                                         "include": ["src/b.ts"]}, indent=2))
    c.diag(a)
    c.diag(b)
    c.tr.request("custom/projectInfo", a.td())
    c.tr.request("custom/projectInfo", b.td())
    c.tr.request("textDocument/references", {**a.tdp(c.at(a, "f(x)")), "context": {"includeDeclaration": True}})
    c.remove("tsconfig.json")
    c.diag(a)
    c.tr.request("custom/projectInfo", a.td())
    return c


def case_fs_package_json() -> Case:
    c = Case("fs-package-json", "package.json type and imports change the module format and resolution",
             {"tsconfig.json": TSCONFIG, "package.json": '{ "name": "p" }\n',
              "src/a.ts": 'import { u } from "#util";\nexport const here = import.meta.url + u;\n',
              "src/util.ts": 'export const u = "u";\n'})
    a = c.open("src/a.ts")
    c.diag(a)
    c.write("package.json", '{ "name": "p", "type": "module" }\n')
    c.diag(a)
    c.write("package.json", '{ "name": "p", "type": "module", "imports": { "#util": "./src/util.js" } }\n')
    c.diag(a)
    c.tr.request("textDocument/definition", a.tdp(c.at(a, "u }")))
    c.tr.request("textDocument/completion", {**a.tdp(c.at(a, "#util") + 1),
                                             "context": {"triggerKind": 2, "triggerCharacter": "#"}})
    c.write("package.json", '{ "name": "p", "type": "commonjs", "imports": { "#util": "./src/util.js" } }\n')
    c.diag(a)
    return c


def case_fs_node_modules() -> Case:
    c = Case("fs-node-modules", "a package appears in node_modules, then its types change",
             {"tsconfig.json": TSCONFIG, "package.json": '{ "type": "module" }\n',
              "src/a.ts": 'import { greet } from "greeter";\nexport const s: string = greet("x");\n'})
    a = c.open("src/a.ts")
    c.diag(a)
    c.write("node_modules/greeter/package.json",
            '{ "name": "greeter", "type": "module", "exports": { ".": { "types": "./index.d.ts" } } }\n', notify=False)
    c.write("node_modules/greeter/index.d.ts", "export declare function greet(n: string): string;\n", notify=False)
    c.watched([("node_modules/greeter/package.json", CREATED), ("node_modules/greeter/index.d.ts", CREATED)])
    c.diag(a)
    c.tr.request("textDocument/hover", a.tdp(c.at(a, "greet(")))
    c.tr.request("custom/textDocument/sourceDefinition", a.tdp(c.at(a, "greet(")))
    c.write("node_modules/greeter/index.d.ts", "export declare function greet(n: number): number;\n")
    c.diag(a)
    c.tr.request("textDocument/signatureHelp", {**a.tdp(c.at(a, '"x"')),
                                                "context": {"triggerKind": 1, "isRetrigger": False}})
    return c


def case_fs_closed_and_open() -> Case:
    c = Case("fs-closed-and-open", "disk changes to a closed dependency and to an open file (the overlay wins)",
             {"tsconfig.json": TSCONFIG, "package.json": '{ "type": "module" }\n',
              "src/a.ts": 'import { dep } from "./dep.js";\nexport const v: number = dep;\n',
              "src/dep.ts": "export const dep = 1;\n"})
    a = c.open("src/a.ts")
    c.diag(a)
    c.write("src/dep.ts", "export const dep2 = 1;\n")
    c.diag(a)
    c.tr.request("textDocument/codeAction", {**a.td(), "range": a.full(),
                                             "context": {"diagnostics": [], "only": ["source.organizeImports"]}})
    c.write("src/a.ts", "export const broken: = ;\n")
    c.diag(a)
    c.tr.request("textDocument/hover", a.tdp(c.at(a, "v:")))
    a.change(c.tr, [(0, len(a.text), b'import { dep2 } from "./dep.js";\nexport const v: number = dep2;\n')])
    c.diag(a)
    c.close("src/a.ts")
    d = Doc("src/a.ts", c.disk["src/a.ts"].encode(), UTF16)
    c.tr.request("textDocument/diagnostic", d.td())
    c.tr.request("textDocument/documentSymbol", d.td())
    return c


def case_isolated_declarations() -> Case:
    text = ("import { helper } from './helper.js';\n"
            "export function add(a: number, b: number) {\n  return a + b;\n}\n"
            "export const total = add(1, 2);\n"
            "export const pair = { left: helper(), right: [1, 2] as const };\n"
            "export class Box {\n  value = helper();\n  get size() { return 1; }\n  method(x: string) { return x.length; }\n}\n"
            "export default { add };\n"
            "export const arrow = (n: number) => n * 2;\n")
    c = Case("isolated-declarations", "isolatedDeclarations errors and their type annotation fixes",
             {"tsconfig.json": json.dumps({"compilerOptions": {
                 "strict": True, "module": "nodenext", "declaration": True, "isolatedDeclarations": True}}, indent=2),
              "package.json": '{ "type": "module" }\n',
              "src/helper.ts": "export function helper(): { id: number } { return { id: 1 }; }\n",
              "src/a.ts": text})
    a = c.open("src/a.ts")
    d = c.diag(a)
    quickfixes(c.tr, a, d, 10)
    all_diagnostics_action(c.tr, a, d)
    source_action(c.tr, a, ["source.fixAll"])
    source_action(c.tr, a, None, a.full())
    return c


def case_implement_interface() -> Case:
    c = Case("implement-interface", "implement an interface whose member types come from other modules",
             {"tsconfig.json": TSCONFIG, "package.json": '{ "type": "module" }\n',
              "src/types.ts": "export interface Opts { depth: number; tags?: readonly string[] }\n"
                              "export type Result<T> = { ok: true; value: T } | { ok: false; error: Error };\n",
              "src/shape.ts": 'import type { Opts, Result } from "./types.js";\n'
                              "export interface Shape<T = number> {\n  readonly id: string;\n"
                              "  area(opts?: Opts): Result<T>;\n  scale?(by: number): this;\n"
                              "  [key: `x-${string}`]: unknown;\n  get name(): string;\n}\n",
              "src/impl.ts": 'import { Shape } from "./shape.js";\n\nexport class Square implements Shape<bigint> {}\n'
                             "export class Circle implements Shape {\n  readonly id = 'c';\n}\n"})
    a = c.open("src/impl.ts")
    d = c.diag(a)
    quickfixes(c.tr, a, d, 4)
    source_action(c.tr, a, ["source.fixAll"])
    configure(c.tr, PREF_VARIANTS[0])
    quickfixes(c.tr, a, d, 1)
    configure(c.tr, None)
    return c


def case_push_diagnostics() -> Case:
    bad = json.dumps({"compilerOptions": {"strict": True, "notAnOption": 1, "module": "nodenext"}}, indent=2)
    c = Case("push-diagnostics", "push diagnostics for tsconfig.json, before and after a fix",
             {"tsconfig.json": bad, "src/a.ts": "export const a: number = 'x';\n"}, push=True)
    a = c.open("src/a.ts")
    c.diag(a)
    c.tr.request("textDocument/hover", a.tdp(c.at(a, "a:")))
    c.write("tsconfig.json", TSCONFIG)
    c.diag(a)
    c.tr.request("textDocument/hover", a.tdp(c.at(a, "a:")))
    return c


INLINE_CASES = [
    lambda: case_fs_add_delete_rename(False), lambda: case_fs_add_delete_rename(True), case_fs_tsconfig,
    case_fs_package_json, case_fs_node_modules, case_fs_closed_and_open, case_isolated_declarations,
    case_implement_interface, case_push_diagnostics,
]


def inline_part(out_dir: Path) -> list[dict]:
    return [make().entry(out_dir) for make in INLINE_CASES]


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

PARTS = {
    **{f"{BATTERY}-{p['name']}": (lambda out, p=p: project_part(p, out)) for p in PROJECTS},
    f"{BATTERY}-utf8": utf8_part,
    f"{BATTERY}-inline": inline_part,
}


def cmd_build(args) -> int:
    out_dir = Path(args.out)
    lb.guard_out(out_dir, [p["root"] for p in PROJECTS] + [INPUTS, lb.BATTERY_DIR])
    names = args.parts.split(",") if args.parts else list(PARTS)
    index = {"format": "goport-lsp-battery-index/1", "battery": BATTERY,
             "generatorSha256": lb.file_sha(Path(__file__)), "lspBatterySha256": lb.file_sha(LSP_BATTERY_PY),
             "lspBattery": str(LSP_BATTERY_PY), "parts": []}
    for name in names:
        if name not in PARTS:
            raise SystemExit(f"unknown part {name}; parts: {', '.join(PARTS)}")
        traces = PARTS[name](out_dir)
        index["parts"].append({"name": name, "kind": "edits", "schedule": "manual", "traces": traces})
    index["traceSetSha256"] = hashlib.sha256("".join(
        f"{t['name']} {t['sha256']}\n" for p in index["parts"] for t in p["traces"]).encode()).hexdigest()
    (out_dir / f"{BATTERY}.index.json").write_text(json.dumps(index, indent=1) + "\n")
    lb.print_summary(index["parts"])
    return 0


def cmd_list(_args) -> int:
    for name in PARTS:
        print(name)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build", help="write the edit-flow traces")
    b.add_argument("--out", required=True, help="traces root")
    b.add_argument("--parts", help="comma list of parts (default: all)")
    sub.add_parser("list", help="print the part names")
    args = ap.parse_args()
    return {"build": cmd_build, "list": cmd_list}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
