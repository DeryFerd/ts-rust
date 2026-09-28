#!/usr/bin/env python3
"""Editor-session benchmark: Rust goport tsgo against Go tsgo-oracle, same messages, one server at a time.

Each session starts `tsgo --lsp --stdio` in a project directory, opens files as overlays (didOpen,
didChange only; the project input is never written) and makes a fixed list of edits. After each edit
the client sends a burst of requests and waits for all answers, as an editor does. Go runs first,
then each Rust binary, with the same messages (the plan is fixed before any server starts). On Linux
each server is pinned with taskset. A server is killed if its RSS goes over --rss-cap-mib.

Scenarios (edits per session in brackets):
  typing   [40]  append one character per edit at the end of the main file; pull diagnostics
  errfix   [40]  insert a type error in the middle of the file, then fix it (2 edits per error);
                 diagnostics and a codeAction with that diagnostic
  mix      [40]  type a statement in the middle of the file; after each character a VS Code-like
                 burst: diagnostic, completion (word start or "."; auto-imports on), codeAction,
                 inlayHint (visible range), semanticTokens/full, documentSymbol, hover
  imports  [40]  multi-file: add an export to a second open file, use it in the main file
                 (missing-name error, quick fix, completion), add the import, remove both, remove
                 the export (5 edits per cycle); pull diagnostics for both files
  long     [200] all of the above interleaved: per 20 edits, 10 typing, 2 errfix, 5 imports, 3 mix
Projects: query-core, hono, effect (target/project-inputs/*/source, read-only).

Per session: RSS after the open (edit 0) and after every edit, VmHWM, edit latency (didChange to the
answer of the edited file's diagnostics, the first request of every burst), round latency (didChange
to the last answer), per-method times and the normalized answers.

Limits (Rust against Go, per project and scenario; see LIMITS). Any failure makes the exit status 1:
  growth       RSS growth per edit (slope over the second half) <= 2 x Go + 1 MiB, in sessions of
               100+ edits only (the long session by default); shorter sessions report it
  rss          RSS added by the edits (last edit minus edit 0) <= 2 x Go + 256 MiB
  editMedian   median edit latency <= 1.5 x Go + 5 ms
  editP95      p95 edit latency <= 2 x Go + 20 ms
  roundMedian  median round latency <= 2 x Go + 10 ms
  answers      no Rust error, crash, timeout or RSS-cap kill where Go answered
Answer equality (normalized; completion items sorted) is reported per method, not judged: Go itself
is not always stable there (auto-import module specifiers).

Usage:
  ls_edit_bench.py --rust [LABEL=]BIN [--rust ...] [--go BIN] [--projects query-core,hono,effect]
                   [--scenarios typing,errfix,mix,imports,long] [--edits 40] [--long-edits 200]
                   [--cpus 8,10,12,14] [--rss-cap-mib 12288] [--out DIR]
  ls_edit_bench.py --recheck --out DIR    apply the current limits to DIR/result.json again
Another upstream pin: GOPORT_PIN=<key> scripts/upstream/pin.py exec -- scripts/goport/ls_edit_bench.py ...
(pin.py maps ~/.local/bin/tsgo-oracle to the pin's oracle; the result records the oracle sha256).

Outputs in --out: result.json (all rows and summaries), report.md (tables). Exit 0 within limits,
1 a limit failed, 2 usage error or a Go session failed.
"""

import argparse
import datetime
import hashlib
import json
import os
import queue
import shutil
import socket
import statistics
import subprocess
import sys
import tempfile
import threading
import time
import urllib.parse
import zlib

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INPUTS = os.path.join(REPO, "target/project-inputs")
GO = os.path.expanduser("~/.local/bin/tsgo-oracle")
PINNED = bool(shutil.which("taskset") and shutil.which("setpriv"))

# root: server cwd and rootUri. main: the edited file. dep: a second open file that main can import
# (imports scenario). spec: the import specifier for dep as written in main's module style.
PROJECTS = {
    "query-core": {"root": f"{INPUTS}/query/source/packages/query-core", "main": "src/queryObserver.ts",
                   "dep": "src/utils.ts", "spec": "'./utils'"},
    "hono": {"root": f"{INPUTS}/hono/source", "main": "src/hono-base.ts", "dep": "src/utils/url.ts",
             "spec": "'./utils/url'"},
    "effect": {"root": f"{INPUTS}/effect/source/packages/effect", "main": "src/Option.ts",
               "dep": "src/Predicate.ts", "spec": '"./Predicate.ts"'},
}

# VS Code-like settings (same as the lsmem editor-mix repro). Auto-imports on; inlay hints on so the
# inlayHint request does checker work; ATA off (no network).
CONFIG = {
    "js/ts": {
        "tsserver": {"automaticTypeAcquisition": {"enabled": False}},
        "suggest": {"autoImports": True, "includeCompletionsForImportStatements": True},
        "preferences": {"includePackageJsonAutoImports": "auto"},
        "inlayHints": {
            "parameterNames": {"enabled": "all", "suppressWhenArgumentMatchesName": False},
            "parameterTypes": {"enabled": True},
            "variableTypes": {"enabled": True, "suppressWhenTypeMatchesName": False},
            "propertyDeclarationTypes": {"enabled": True},
            "functionLikeReturnTypes": {"enabled": True},
            "enumMemberValues": {"enabled": True},
        },
    },
    "typescript": None,
    "javascript": None,
    "editor": None,
}

# Client capabilities: the oracle defaults (lsp_oracle.py get_capabilities_with_defaults, utf-16).
MARKDOWN_PLAIN = ["markdown", "plaintext"]
DIAG_TAGS = {"valueSet": [1, 2]}
CAPABILITIES = {
    "general": {"positionEncodings": ["utf-16"]},
    "experimental": {"hoverVerbosityLevel": True},
    "textDocument": {
        "completion": {
            "completionItem": {"snippetSupport": True, "commitCharactersSupport": True, "preselectSupport": True,
                               "labelDetailsSupport": True, "insertReplaceSupport": True,
                               "documentationFormat": MARKDOWN_PLAIN},
            "completionList": {"itemDefaults": ["commitCharacters", "editRange"]},
        },
        "diagnostic": {"relatedInformation": True, "tagSupport": DIAG_TAGS},
        "publishDiagnostics": {"relatedInformation": True, "tagSupport": DIAG_TAGS},
        "semanticTokens": {
            "requests": {"full": True},
            "tokenTypes": ["namespace", "class", "enum", "interface", "struct", "typeParameter", "type", "parameter",
                           "variable", "property", "enumMember", "decorator", "event", "function", "method", "macro",
                           "label", "comment", "string", "keyword", "number", "regexp", "operator"],
            "tokenModifiers": ["declaration", "definition", "readonly", "static", "deprecated", "abstract", "async",
                               "modification", "documentation", "defaultLibrary", "local"],
            "formats": ["relative"],
        },
        "definition": {"linkSupport": True},
        "hover": {"contentFormat": MARKDOWN_PLAIN},
        "signatureHelp": {"signatureInformation": {"documentationFormat": MARKDOWN_PLAIN,
                                                   "parameterInformation": {"labelOffsetSupport": True},
                                                   "activeParameterSupport": True},
                          "contextSupport": True},
        "documentSymbol": {"hierarchicalDocumentSymbolSupport": True},
        "codeAction": {"codeActionLiteralSupport": {"codeActionKind": {"valueSet": [
            "", "quickfix", "refactor", "refactor.extract", "refactor.inline", "refactor.rewrite", "source",
            "source.organizeImports"]}}, "resolveSupport": {"properties": ["edit"]}},
    },
    "workspace": {"workspaceEdit": {"documentChanges": True}, "configuration": True},
}

# (name, summary field, factor, allowance, unit, text): Rust must be <= factor x max(Go, 0) + allowance.
# Growth is judged only in sessions of at least GROWTH_MIN_EDITS edits (by default the long session):
# Go's heap still grows for about 30 edits and its GC sawtooth is about +-50 MiB, so a slope over the
# last 20 edits of a 40-edit session is too noisy (two runs of R122 and R123 gave different verdicts in
# 9 of 24 such checks). Shorter sessions report growth without judging it.
GROWTH_MIN_EDITS = 100
LIMITS = [
    ("growth", "growthMiBPerEdit", 2, 1, "MiB/edit",
     f"RSS growth per edit (least-squares slope over the second half of the edits; sessions of "
     f"{GROWTH_MIN_EDITS}+ edits) <= 2 x Go + 1 MiB"),
    ("rss", "rssAdded", 2, 256, "MiB", "RSS added by the edits (last edit minus edit 0) <= 2 x Go + 256 MiB"),
    ("editMedian", "editMedianMs", 1.5, 5, "ms", "median edit latency <= 1.5 x Go + 5 ms"),
    ("editP95", "editP95Ms", 2, 20, "ms", "p95 edit latency <= 2 x Go + 20 ms"),
    ("roundMedian", "roundMedianMs", 2, 10, "ms", "median round latency <= 2 x Go + 10 ms"),
]
CHECKPOINTS = (0, 20, 40, 200)


# ---------------------------------------------------------------------------
# Documents and edit plans. A plan is fixed before any server starts, so every side gets the same
# messages. Positions come from the client's own copy of the text, never from server answers.
# ---------------------------------------------------------------------------


def utf16_len(s):
    return len(s.encode("utf-16-le")) // 2


def is_ident(c):
    return c.isalnum() or c in "_$"


class Doc:
    """One open file: text, version and named offsets (marks) that move with edits.
    A mark at an insertion point moves after the inserted text."""

    def __init__(self, root, rel):
        path = os.path.join(root, rel)
        self.uri = "file://" + urllib.parse.quote(path)
        with open(path, encoding="utf-8") as f:
            self.text = f.read()
        self.version = 1
        self.marks = {}

    def pos(self, off):
        start = self.text.rfind("\n", 0, off) + 1
        return {"line": self.text.count("\n", 0, off), "character": utf16_len(self.text[start:off])}

    def rng(self, a, b):
        return {"start": self.pos(a), "end": self.pos(b)}

    def open(self):
        return ["textDocument/didOpen", {"textDocument": {"uri": self.uri, "languageId": "typescript",
                                                          "version": self.version, "text": self.text}}]

    def change(self, *edits):
        """didChange with one range change per (start, end, new). Each edit is against the text after
        the edits before it, as LSP applies them."""
        changes = []
        for a, b, new in edits:
            changes.append({"range": self.rng(a, b), "text": new})
            self.text = self.text[:a] + new + self.text[b:]
            delta = len(new) - (b - a)
            for k, m in self.marks.items():
                if m >= b:
                    self.marks[k] = m + delta
                elif m > a:
                    self.marks[k] = a
        self.version += 1
        return ["textDocument/didChange", {"textDocument": {"uri": self.uri, "version": self.version},
                                           "contentChanges": changes}]

    def boundaries(self):
        """Offsets where a new top-level statement can go: the newline that ends a blank line
        before a top-level declaration."""
        out, off, prev = [], 0, None
        starts = ("export ", "/**", "function ", "const ", "class ", "interface ", "type ")
        for line in self.text.split("\n"):
            if prev == "" and line.startswith(starts):
                out.append(off - 1)
            off += len(line) + 1
            prev = line
        return out


def diag(doc):
    return ["textDocument/diagnostic", {"textDocument": {"uri": doc.uri}}]


def code_action(doc, rng, diagnostics):
    return ["textDocument/codeAction", {"textDocument": {"uri": doc.uri}, "range": rng,
                                        "context": {"diagnostics": diagnostics, "triggerKind": 2}}]


def completion(doc, pos, trigger=None):
    ctx = {"triggerKind": 2, "triggerCharacter": trigger} if trigger else {"triggerKind": 1}
    return ["textDocument/completion", {"textDocument": {"uri": doc.uri}, "position": pos, "context": ctx}]


def mix_requests(doc, off, typed=""):
    """The VS Code-like burst at the cursor `off`. `typed` is the character just typed (completion
    runs at a word start or after ".", like quick suggestions)."""
    tdoc = {"uri": doc.uri}
    cur = doc.pos(off)
    before = doc.text[off - 2] if off >= 2 else "\n"
    reqs = [diag(doc)]
    if typed == ".":
        reqs.append(completion(doc, cur, "."))
    elif typed and is_ident(typed) and not is_ident(before):
        reqs.append(completion(doc, cur))
    last = doc.text.count("\n")
    reqs += [
        code_action(doc, {"start": cur, "end": cur}, []),
        ["textDocument/inlayHint", {"textDocument": tdoc, "range": {
            "start": {"line": max(0, cur["line"] - 30), "character": 0},
            "end": {"line": min(last, cur["line"] + 30), "character": 0}}}],
        ["textDocument/semanticTokens/full", {"textDocument": tdoc}],
        ["textDocument/documentSymbol", {"textDocument": tdoc}],
        ["textDocument/hover", {"textDocument": tdoc, "position": doc.pos(max(0, off - 1))}],
    ]
    return reqs


class Plan:
    def __init__(self, project):
        p = PROJECTS[project]
        self.main = Doc(p["root"], p["main"])
        self.dep = Doc(p["root"], p["dep"])
        self.spec = p["spec"]
        # a1: errfix and imports insert here. a2: mix types here. Two different top-level boundaries,
        # near 40% and 70% of the file when the file has them.
        b = self.main.boundaries()
        if len(b) < 2:
            raise SystemExit(f"ls_edit_bench: {p['main']} has fewer than 2 top-level boundaries")
        n = len(self.main.text)
        a1 = next((x for x in b if x >= 0.4 * n), b[-1])
        later = [x for x in b if x > a1]
        a2 = next((x for x in later if x >= 0.7 * n), later[0] if later else [x for x in b if x < a1][-1])
        self.main.marks.update(a1=a1, a2=a2)


# Each generator yields one round per edit: (notifications, requests).

def gen_typing(plan):
    doc = plan.main
    k = 0
    while True:
        for ch in f"\nexport const lsTyped{k} = [1, 2, 3].map((n) => n * 2).filter(Boolean).length + {k}":
            end = len(doc.text)
            yield [doc.change((end, end, ch))], [diag(doc)]
        k += 1


def gen_errfix(plan):
    doc = plan.main
    k = 0
    while True:
        name, bad = f"lsBenchErr{k}", f'"e{k}"'
        a = doc.marks["a1"]
        line = f"\nexport const {name}: number = {bad}"
        note = doc.change((a, a, line))
        doc.marks["errv"] = a + line.index(bad)
        n = a + line.index(name)
        d = {"range": doc.rng(n, n + len(name)), "severity": 1, "code": 2322, "source": "ts",
             "message": "Type 'string' is not assignable to type 'number'."}
        yield [note], [diag(doc), code_action(doc, d["range"], [d])]
        v = doc.marks.pop("errv")
        yield [doc.change((v, v + len(bad), str(k)))], [diag(doc)]
        k += 1


def gen_imports(plan):
    a, b = plan.main, plan.dep
    k = 0
    while True:
        name = f"lsBenchShared{k}"
        exp = f"\nexport const {name} = {k}"
        e = len(b.text)
        note = b.change((e, e, exp))
        b.marks["exp"] = e
        yield [note], [diag(b), diag(a)]

        use = f"\nexport const lsBenchUse{k} = {name} + 1"
        p = a.marks["a1"]
        note = a.change((p, p, use))
        a.marks["use"] = p
        s = p + use.index(name)
        r = a.rng(s, s + len(name))
        d = {"range": r, "severity": 1, "code": 2304, "source": "ts", "message": f"Cannot find name '{name}'."}
        yield [note], [diag(a), code_action(a, r, [d]), completion(a, r["end"])]

        imp = f"import {{ {name} }} from {plan.spec}\n"
        yield [a.change((0, 0, imp))], [diag(a)]

        u = a.marks.pop("use")
        yield [a.change((u, u + len(use), ""), (0, len(imp), ""))], [diag(a)]

        x = b.marks.pop("exp")
        yield [b.change((x, x + len(exp), ""))], [diag(b), diag(a)]
        k += 1


def gen_mix(plan):
    doc = plan.main
    k = 0
    while True:
        for ch in f"\nexport const lsMix{k} = new Map<string, number>().size + Math.max({k}, 2)":
            c = doc.marks["a2"]
            note = doc.change((c, c, ch))
            yield [note], mix_requests(doc, doc.marks["a2"], ch)
        k += 1


def gen_long(plan):
    gens = {"typing": gen_typing(plan), "errfix": gen_errfix(plan), "imports": gen_imports(plan),
            "mix": gen_mix(plan)}
    pattern = ["typing"] * 10 + ["errfix"] * 2 + ["imports"] * 5 + ["mix"] * 3
    i = 0
    while True:
        yield next(gens[pattern[i % len(pattern)]])
        i += 1


# name: (generator, default edit count, dep file open, mix burst in the open round)
SCENARIOS = {
    "typing": (gen_typing, 40, False, False),
    "errfix": (gen_errfix, 40, False, False),
    "mix": (gen_mix, 40, False, True),
    "imports": (gen_imports, 40, True, False),
    "long": (gen_long, 200, True, True),
}


def build_plan(project, scenario, edits):
    """Rounds: round 0 opens the files, rounds 1..edits are the edits."""
    gen, _, with_dep, open_mix = SCENARIOS[scenario]
    plan = Plan(project)
    docs = [plan.main, plan.dep] if with_dep else [plan.main]
    reqs = mix_requests(plan.main, plan.main.marks["a2"]) if open_mix else [diag(plan.main)]
    reqs += [diag(d) for d in docs[1:]]
    rounds = [([d.open() for d in docs], reqs)]
    it = gen(plan)
    rounds += [next(it) for _ in range(edits)]
    root = PROJECTS[project]["root"]
    digest = hashlib.sha256(json.dumps(rounds, sort_keys=True).replace(root, "@ROOT@").encode()).hexdigest()[:12]
    return rounds, digest


# ---------------------------------------------------------------------------
# LSP client (Content-Length framing, as in lsp_oracle.py and Go jsonrpc/baseproto.go)
# ---------------------------------------------------------------------------


class ServerDied(Exception):
    pass


class Server:
    """One `tsgo --lsp --stdio` process, killed if RSS goes over `cap_mib`. On Linux it is pinned with
    taskset and dies with the harness (setpriv); elsewhere (macOS) it runs unpinned."""

    def __init__(self, binary, cwd, cpus, home, cap_mib, extra_env):
        env = dict(os.environ, HOME=home, XDG_CACHE_HOME=f"{home}/.cache", XDG_CONFIG_HOME=f"{home}/.config",
                   XDG_DATA_HOME=f"{home}/.local/share", **extra_env)
        argv = [binary, "--lsp", "--stdio"]
        if PINNED:
            argv = ["setpriv", "--pdeathsig", "KILL", "taskset", "-c", cpus, *argv]
        self.peak = 0
        self.proc = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)
        self.inbox = queue.Queue()
        self.stderr = []
        self.capped = False
        self.cap_mib = cap_mib
        self.id = 0
        for fn in (self._read, self._drain_stderr, self._watch_rss):
            threading.Thread(target=fn, daemon=True).start()

    def _read(self):
        out = self.proc.stdout
        try:
            while True:
                length = None
                while True:
                    line = out.readline()
                    if not line:
                        raise EOFError
                    if line == b"\r\n":
                        break
                    key, _, value = line.partition(b":")
                    if key.strip().lower() == b"content-length":
                        length = int(value)
                body = out.read(length)
                if len(body) != length:
                    raise EOFError
                self.inbox.put(json.loads(body))
        except (EOFError, ValueError, OSError, TypeError):
            self.inbox.put(None)

    def _drain_stderr(self):
        for line in self.proc.stderr:
            self.stderr = (self.stderr + [line.decode("utf-8", "replace").rstrip()[:300]])[-20:]

    def _watch_rss(self):
        while self.proc.poll() is None:
            if self.mem().get("rss", 0) > self.cap_mib:
                self.capped = True
                self.proc.kill()
                return
            time.sleep(0.25)

    def mem(self):
        """RSS and peak RSS in MiB. Linux reads /proc (VmHWM is the kernel's peak). Elsewhere `ps` gives
        RSS and the peak is the highest RSS seen (the watchdog samples every 0.25 s)."""
        pid = self.proc.pid
        if os.path.exists("/proc/self/status"):
            out = {}
            try:
                with open(f"/proc/{pid}/status") as f:
                    for line in f:
                        k, _, v = line.partition(":")
                        if k in ("VmRSS", "VmHWM"):
                            out["rss" if k == "VmRSS" else "hwm"] = int(v.split()[0]) // 1024
            except OSError:
                pass
            return out
        ps = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True).stdout.split()
        if not ps:
            return {}
        self.peak = max(self.peak, int(ps[0]) // 1024)
        return {"rss": int(ps[0]) // 1024, "hwm": self.peak}

    def send(self, msg):
        data = json.dumps(msg, ensure_ascii=False, separators=(",", ":")).encode()
        try:
            self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
            self.proc.stdin.flush()
        except OSError as e:
            raise ServerDied(f"write failed: {e}") from None

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def answer(self, req):
        m = req.get("method")
        if m == "workspace/configuration":
            items = (req.get("params") or {}).get("items") or []
            reply = {"result": [CONFIG.get(it.get("section")) for it in items]}
        elif m in ("client/registerCapability", "client/unregisterCapability", "window/workDoneProgress/create"):
            reply = {"result": None}
        else:
            reply = {"error": {"code": -32601, "message": f"Unknown method: {m}"}}
        self.send({"jsonrpc": "2.0", "id": req.get("id"), **reply})

    def burst(self, reqs, timeout):
        """Sends all requests, then waits for all answers. Returns [(ms, message)] in request order."""
        t0 = time.monotonic()
        ids = []
        for method, params in reqs:
            self.id += 1
            ids.append(self.id)
            msg = {"jsonrpc": "2.0", "id": self.id, "method": method}
            if params is not None:
                msg["params"] = params
            self.send(msg)
        got = {}
        deadline = t0 + timeout
        while len(got) < len(ids):
            try:
                msg = self.inbox.get(timeout=max(0.0, deadline - time.monotonic()))
            except queue.Empty:
                raise ServerDied(f"timeout after {timeout:.0f} s") from None
            if msg is None:
                self.inbox.put(None)
                why = "RSS over the cap" if self.capped else f"exit {self.proc.poll()}"
                raise ServerDied(f"server ended ({why}): {self.stderr[-3:]}")
            if "method" in msg:
                if "id" in msg:
                    self.answer(msg)
                continue
            if msg.get("id") in ids:
                got[msg["id"]] = ((time.monotonic() - t0) * 1000, msg)
        return [got[i] for i in ids]

    def close(self):
        try:
            self.burst([["shutdown", None]], 30)
            self.notify("exit", None)
        except ServerDied:
            pass
        try:
            self.proc.stdin.close()
        except OSError:
            pass
        try:
            return self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            return self.proc.wait()


# ---------------------------------------------------------------------------
# Sessions, comparison and limits
# ---------------------------------------------------------------------------


def canon(v):
    return json.dumps(v, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def normalize(method, msg):
    if "error" in msg:
        return {"error": str((msg["error"] or {}).get("message", "")).split("\n", 1)[0]}
    result = msg.get("result")
    if method == "textDocument/completion":  # Go map order makes the item order random
        if isinstance(result, dict) and isinstance(result.get("items"), list):
            result = dict(result, items=sorted(result["items"], key=canon))
        elif isinstance(result, list):
            result = sorted(result, key=canon)
    return {"result": result}


def first_diff(a, b, path=""):
    if type(a) is not type(b):
        return path or "/"
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a or k not in b:
                return f"{path}/{k}"
            d = first_diff(a[k], b[k], f"{path}/{k}")
            if d is not None:
                return d
        return None
    if isinstance(a, list):
        for i, (x, y) in enumerate(zip(a, b)):
            d = first_diff(x, y, f"{path}/{i}")
            if d is not None:
                return d
        return None if len(a) == len(b) else f"{path}/length"
    return None if a == b else (path or "/")


def value_at(v, path, limit=200):
    """Short text of the value at a first_diff path ("-" when it is missing)."""
    for part in path.strip("/").split("/") if path.strip("/") else []:
        if isinstance(v, dict) and part in v:
            v = v[part]
        elif isinstance(v, list) and part.isdigit() and int(part) < len(v):
            v = v[int(part)]
        else:
            return "-"
    return canon(v)[:limit]


def sha256_12(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()[:12]


def run_session(args, project, rounds, binary, extra_env=None):
    """Runs one server through all rounds. Returns (session record, answers). answers[r][i] is the
    zlib-compressed canonical normalized answer of request i in round r."""
    home = tempfile.mkdtemp(prefix="ls-edit-bench-")
    root = PROJECTS[project]["root"]
    server = Server(binary, root, args.cpus, home, args.rss_cap_mib, extra_env or {})
    rows, answers, error, init_ms = [], [], None, None
    try:
        init = {"processId": None, "rootUri": "file://" + urllib.parse.quote(root), "locale": "en-US",
                "capabilities": CAPABILITIES,
                "initializationOptions": {"disablePushDiagnostics": True, "logVerbosity": 0}}
        t0 = time.monotonic()
        server.burst([["initialize", init]], args.timeout)
        server.notify("initialized", {})
        init_ms = (time.monotonic() - t0) * 1000
        for n, (notes, reqs) in enumerate(rounds):
            t = time.monotonic()
            for method, params in notes:
                server.notify(method, params)
            res = server.burst(reqs, args.timeout)
            ms = (time.monotonic() - t) * 1000
            row = {"edit": n, "ms": round(ms, 2), **server.mem(), "req": []}
            got = []
            for (method, _), (rms, msg) in zip(reqs, res):
                norm = normalize(method, msg)
                row["req"].append([method, round(rms, 2), "error" if "error" in norm else "ok"])
                got.append(zlib.compress(canon(norm).encode(), 1))
            rows.append(row)
            answers.append(got)
    except ServerDied as e:
        error = str(e)
    finally:
        idle = server.mem()
        code = server.close()
        shutil.rmtree(home, ignore_errors=True)
    rec = {"binary": binary, "sha256": sha256_12(binary), "initMs": init_ms and round(init_ms, 1),
           "error": error, "exit": code, "idle": idle, "rows": rows}
    return rec, answers


def median(xs):
    return statistics.median(xs) if xs else None


def p95(xs):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(0.95 * (len(xs) - 1))))] if xs else None


def slope(points):
    """Least-squares slope of (x, y) points."""
    if len(points) < 2:
        return None
    mx = sum(x for x, _ in points) / len(points)
    my = sum(y for _, y in points) / len(points)
    den = sum((x - mx) ** 2 for x, _ in points)
    return sum((x - mx) * (y - my) for x, y in points) / den if den else None


def summarize(rec, edits):
    rows = rec["rows"]
    done = [r for r in rows if r["edit"] >= 1]
    edit_ms = [r["req"][0][1] for r in done]  # every round starts with the edited file's diagnostics
    round_ms = [r["ms"] for r in done]
    growth = slope([(r["edit"], r["rss"]) for r in rows if r["edit"] >= max(1, edits // 2) and "rss" in r])
    by_method = {}
    for r in done:
        for method, rms, _ in r["req"]:
            by_method.setdefault(method, []).append(rms)
    return {
        "complete": rec["error"] is None and len(rows) == edits + 1,
        "edits": len(done),
        "rssAt": {str(c): rows[c].get("rss") for c in CHECKPOINTS if c < len(rows)},
        "rssEnd": rows[-1].get("rss") if rows else None,
        "rssAdded": rows[-1]["rss"] - rows[0]["rss"] if rows and "rss" in rows[0] and "rss" in rows[-1] else None,
        "hwm": rows[-1].get("hwm") if rows else None,
        "growthMiBPerEdit": None if growth is None else round(growth, 3),
        "editMedianMs": median(edit_ms), "editP95Ms": p95(edit_ms),
        "roundMedianMs": median(round_ms), "roundP95Ms": p95(round_ms),
        "methods": {m: {"n": len(v), "medianMs": round(median(v), 2), "p95Ms": round(p95(v), 2)}
                    for m, v in sorted(by_method.items())},
        "errors": sum(1 for r in rows for _, _, st in r["req"] if st == "error"),
    }


def compare(rounds, go_answers, rust_answers):
    """Per method: same, differ, and the first few differing requests with the first differing path."""
    out = {}
    for n, (go_round, rust_round) in enumerate(zip(go_answers, rust_answers)):
        for i, (g, r) in enumerate(zip(go_round, rust_round)):
            method = rounds[n][1][i][0]
            m = out.setdefault(method, {"same": 0, "differ": 0, "examples": []})
            if g == r:
                m["same"] += 1
                continue
            gv, rv = json.loads(zlib.decompress(g)), json.loads(zlib.decompress(r))
            if gv == rv:
                m["same"] += 1
                continue
            m["differ"] += 1
            if len(m["examples"]) < 3:
                path = first_diff(gv, rv)
                m["examples"].append({"edit": n, "request": i, "path": path,
                                      "go": value_at(gv, path), "rust": value_at(rv, path)})
    return out


def check_limits(go, rust, go_rec, rust_rec):
    """Returns {limit: [ok, text]}."""
    if rust_rec["error"] or not rust["complete"]:
        return {"answers": [False, f"session did not finish: {rust_rec['error']}"]}
    out = {}
    for key, field, factor, extra, unit, _ in LIMITS:
        if key == "growth" and rust["edits"] < GROWTH_MIN_EDITS:
            continue
        g, r = go[field], rust[field]
        lim = factor * max(g, 0) + extra
        out[key] = [r <= lim, f"{r:.2f} {unit} (limit {lim:.2f}, Go {g:.2f})"]
    extra = sum(1 for gr, rr in zip(go_rec["rows"], rust_rec["rows"])
                for (_, _, gs), (_, _, rs) in zip(gr["req"], rr["req"]) if rs == "error" and gs == "ok")
    out["answers"] = [extra == 0, f"{extra} Rust errors where Go answered"]
    return out


def fmt(v, digits=1):
    return "-" if v is None else f"{v:.{digits}f}" if isinstance(v, float) else str(v)


def report_md(result):
    lines = ["# ls_edit_bench", "", f"Date {result['date']}, host {result['host']}, CPUs {result['cpus']}. "
             f"Go `{result['go']['binary']}` sha256 `{result['go']['sha256']}`"
             f"{' (GOPORT_PIN ' + result['pin'] + ')' if result['pin'] else ''}.", ""]
    for label, b in result["rust"].items():
        lines.append(f"- Rust `{label}`: `{b['binary']}` sha256 `{b['sha256']}`")
    if result.get("rustEnv"):
        lines.append(f"- Rust environment: `{' '.join(f'{k}={v}' for k, v in result['rustEnv'].items())}`")
    lines += ["", "Limits (Rust against Go):", ""] + [f"- {name}: {text}" for name, *_, text in LIMITS]
    lines += ["- answers: no Rust error, crash, timeout or RSS-cap kill where Go answered", "",
              "Edit latency: didChange to the diagnostics of the edited file. Round: didChange to the last answer.", "",
              "| project | scenario | side | RSS 0/20/40/200 MiB | end | added | HWM | growth MiB/edit | edit median ms "
              "| edit p95 ms | round median ms | answers same/differ | verdict |",
              "|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|"]
    for s in result["sessions"]:
        for side, v in [("go", s["go"])] + list(s["rust"].items()):
            sm = v["summary"]
            rss = "/".join(fmt(sm["rssAt"].get(str(c))) for c in CHECKPOINTS)
            if side == "go":
                eq, verdict = "", "" if v["error"] is None else f"Go failed: {v['error']}"
            else:
                c = v["compare"]
                eq = f"{sum(m['same'] for m in c.values())}/{sum(m['differ'] for m in c.values())}"
                bad = [k for k, (ok, _) in v["limits"].items() if not ok]
                verdict = "pass" if not bad else "FAIL " + ", ".join(bad)
            lines.append(f"| {s['project']} | {s['scenario']} | {side} | {rss} | {fmt(sm['rssEnd'])} | {fmt(sm['rssAdded'])} | {fmt(sm['hwm'])} "
                         f"| {fmt(sm['growthMiBPerEdit'], 2)} | {fmt(sm['editMedianMs'])} | {fmt(sm['editP95Ms'])} "
                         f"| {fmt(sm['roundMedianMs'])} | {eq} | {verdict} |")
    lines += ["", "## Failed limits", ""]
    fails = [(s, side, k, text) for s in result["sessions"] for side, v in s["rust"].items()
             for k, (ok, text) in v["limits"].items() if not ok]
    lines += [f"- {s['project']} {s['scenario']} {side}: {k} {text}" for s, side, k, text in fails] or ["None."]
    lines += ["", "## Answer differences", ""]
    diffs = [(s, side, m, c) for s in result["sessions"] for side, v in s["rust"].items()
             for m, c in v["compare"].items() if c["differ"]]
    lines += [f"- {s['project']} {s['scenario']} {side} `{m}`: {c['differ']} differ, first at "
              + ", ".join(f"edit {e['edit']} `{e['path']}` (Go `{e.get('go')}`, Rust `{e.get('rust')}`)"
                          for e in c["examples"]) for s, side, m, c in diffs] or ["None."]
    lines += ["", "## Median ms per method (Go / Rust)", ""]
    for s in result["sessions"]:
        parts = []
        for m, g in s["go"]["summary"]["methods"].items():
            rs = " / ".join(fmt(v["summary"]["methods"].get(m, {}).get("medianMs")) for v in s["rust"].values())
            parts.append(f"{m.split('/')[-1]} {g['medianMs']} / {rs}")
        lines.append(f"- {s['project']} {s['scenario']}: " + "; ".join(parts))
    return "\n".join(lines) + "\n"


def evaluate(sess):
    """Fills the summaries and limit results of one session record."""
    go = sess["go"]
    go["summary"] = summarize(go, sess["edits"])
    for rec in sess["rust"].values():
        rec["summary"] = summarize(rec, sess["edits"])
        rec["limits"] = check_limits(go["summary"], rec["summary"], go, rec)


def status_of(result):
    """0 within limits, 1 a limit failed, 2 a Go session failed."""
    if any(s["go"]["error"] or not s["go"]["summary"]["complete"] for s in result["sessions"]):
        return 2
    return int(any(not ok for s in result["sessions"] for rec in s["rust"].values() for ok, _ in rec["limits"].values()))


def print_line(project, scenario, label, rec):
    sm = rec["summary"]
    text = (f"{project} {scenario} {label}: RSS {sm['rssAt']} growth {sm['growthMiBPerEdit']} MiB/edit, edit median "
            f"{fmt(sm['editMedianMs'])} p95 {fmt(sm['editP95Ms'])} ms, round median {fmt(sm['roundMedianMs'])} ms")
    if rec["error"]:
        text += f", ERROR {rec['error']}"
    if "limits" in rec:
        failed = [f"{k} {t}" for k, (ok, t) in rec["limits"].items() if not ok]
        differ = sum(m["differ"] for m in rec["compare"].values())
        text += f", {differ} answers differ, " + ("pass" if not failed else "FAIL " + "; ".join(failed))
    print(text, flush=True)


def parse_rust(values):
    out = {}
    for v in values:
        label, sep, path = v.partition("=")
        if not sep:
            path = label
            label = os.path.basename(os.path.dirname(os.path.dirname(path))) or path
        out[label] = os.path.abspath(path)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rust", action="append", default=[], help="[LABEL=]BIN, repeatable")
    ap.add_argument("--go", default=GO)
    ap.add_argument("--rust-env", action="append", default=[],
                    help="KEY=VAL for the Rust servers only, repeatable (for example _RJEM_MALLOC_CONF=narenas:48 "
                         "for jemalloc defaults on a 12-core Mac)")
    ap.add_argument("--projects", default=",".join(PROJECTS))
    ap.add_argument("--scenarios", default=",".join(SCENARIOS))
    ap.add_argument("--edits", type=int, default=0, help="edits for the short scenarios (default 40)")
    ap.add_argument("--long-edits", type=int, default=0, help="edits for the long scenario (default 200)")
    ap.add_argument("--cpus", default="8,10,12,14")
    ap.add_argument("--rss-cap-mib", type=int, default=12288)
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per request burst")
    ap.add_argument("--out", default=os.path.join(REPO, "target/ls-edit-bench",
                                                  datetime.datetime.now().strftime("%Y%m%d-%H%M%S")))
    ap.add_argument("--recheck", action="store_true",
                    help="no servers: apply the current limits to --out/result.json again")
    args = ap.parse_args()
    if args.recheck:
        with open(os.path.join(args.out, "result.json")) as f:
            result = json.load(f)
        for sess in result["sessions"]:
            evaluate(sess)
            for label, rec in sess["rust"].items():
                print_line(sess["project"], sess["scenario"], label, rec)
        with open(os.path.join(args.out, "result.json"), "w") as f:  # rows unchanged, verdicts updated
            json.dump(result, f)
    else:
        rust = parse_rust(args.rust)
        rust_env = dict(kv.split("=", 1) for kv in args.rust_env)
        projects, scenarios = args.projects.split(","), args.scenarios.split(",")
        bad = [p for p in projects if p not in PROJECTS] + [s for s in scenarios if s not in SCENARIOS]
        missing = [b for b in [args.go, *rust.values()] if not os.access(b, os.X_OK)]
        if bad or missing or not rust:
            print(f"ls_edit_bench: need --rust; unknown {bad}; missing binaries {missing}", file=sys.stderr)
            return 2
        os.makedirs(args.out, exist_ok=True)
        result = {"date": datetime.datetime.now().isoformat(timespec="seconds"), "host": socket.gethostname(),
                  "cpus": args.cpus if PINNED else "unpinned", "pin": os.environ.get("GOPORT_PIN_ACTIVE"),
                  "go": {"binary": args.go, "sha256": sha256_12(args.go)},
                  "rust": {k: {"binary": v, "sha256": sha256_12(v)} for k, v in rust.items()},
                  "rustEnv": rust_env, "sessions": []}
        for project in projects:
            for scenario in scenarios:
                edits = (args.long_edits if scenario == "long" else args.edits) or SCENARIOS[scenario][1]
                rounds, digest = build_plan(project, scenario, edits)
                sess = {"project": project, "scenario": scenario, "edits": edits, "plan": digest,
                        "load": round(os.getloadavg()[0], 1), "rust": {}}
                sess["go"], go_answers = run_session(args, project, rounds, args.go)
                sess["go"]["summary"] = summarize(sess["go"], edits)
                print_line(project, scenario, "go", sess["go"])
                if sess["go"]["summary"]["complete"]:
                    for label, binary in rust.items():
                        rec, answers = run_session(args, project, rounds, binary, rust_env)
                        rec["compare"] = compare(rounds, go_answers, answers)
                        sess["rust"][label] = rec
                        evaluate(sess)
                        print_line(project, scenario, label, rec)
                result["sessions"].append(sess)
                with open(os.path.join(args.out, "result.json"), "w") as f:
                    json.dump(result, f)
    status = status_of(result)
    with open(os.path.join(args.out, "report.md"), "w") as f:
        f.write(report_md(result))
    print(f"result: {args.out}/report.md, exit {status}")
    return status


if __name__ == "__main__":
    sys.exit(main())
