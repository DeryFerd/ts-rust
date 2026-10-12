#!/usr/bin/env python3
"""Effect LSP battery e1 for the LSP parity oracle (trace format goport-lsp-trace/1).

The Go side is the effect-tsgo 0.51.1 language server built at the Go pin
(scripts/effect/build-oracle.sh, "E0"), not the plain tsgo oracle: the plain
oracle has no Effect features, so it cannot be the Go side for them. This
script writes the traces and wraps scripts/goport/lsp_oracle.py (protected,
not changed) with the e1 defaults: out root, battery, the E0 oracle, and the
method filter.

Parts (project roots are only read; edits are didChange overlays):
  e1-effect   the effect gate project (project-inputs/effect/source/packages/
              effect, Effect plugin with namespaceImportPackages), every 8th
              file of src/ (as b3s-effect and b5-effect)
  e1-t3code   a T3 Code copy (--t3code, the int52 recipe at e95b57dc): every
              12th .ts file of apps/server, packages/client-runtime and
              packages/shared, and every file where effect-tsgo 0.51.1 reports
              an Effect diagnostic (T3_EFFECT_FILES)
  e1-effect-ce, e1-t3code-ce
              the same files with only the ce requests (below). New parts keep
              the traces and goldens of the parts above as they were.

Requests per file:
  hover       declaration names, namespace members, yield* (at the keyword
              and at the star)
  quickfix    textDocument/diagnostic, then for each of the first 8
              diagnostics (most are Effect ones on the T3 files) codeAction
              with only ["quickfix"] and codeAction with no filter (the
              lightbulb request: quick fixes and refactors)
  refactor    codeAction with no filter on declaration names and call names
  completion  after `X.` for namespace imports; in an appended
              `// @effect-` comment; after `extends ` in an appended class;
              in an appended Duration string. One resolve each.
  autoimport  remove an Effect import, diagnostic, the quick fix for
              "Cannot find name 'X'.", completion at the first use of X and a
              resolve of the X item, then restore the import
  symbols     documentSymbol
  inlay       inlayHint over the file with return type and variable type
              hints on
  ce          (the -ce parts) completion where Effect adds comment and class
              items: in an appended `// @` (trigger "@") and after
              `extends Data.` in an appended class (trigger "."). One resolve
              each. The completion probes above end at `// @effect-` and at
              `extends `, where neither server gives Effect items (effectE6).

Usage:
  lsp_battery_effect.py build [--out-root R] [--parts e1-effect,e1-t3code] [--t3code DIR]
  lsp_battery_effect.py record [--out-root R] [--oracle E0] [--parts P] [--jobs N] [--only S] [--force]
  lsp_battery_effect.py selfcheck [--out-root R] [--oracle E0] [--parts P] [--jobs N] [--runs N (16)]
  lsp_battery_effect.py check --server BIN --label L [--out-root R] [--oracle E0] [--parts P] [--jobs N] [--only S]
  lsp_battery_effect.py list

--parts (a comma list) limits record, selfcheck and check to those parts; the
default is every part (lsp_oracle.py --battery e1). --only matches the file
path in a part, not the part name.

build reads the battery config from lsp-battery/b1.json beside lsp_battery.py.
main has lsp_battery.py but no lsp-battery dir: run build with
LSP_BATTERY_PY=<a checkout that has it, e.g. goport-int7>/scripts/goport/lsp_battery.py
(the same file). A build that adds parts writes the old traces with the same
bytes, so their goldens stay valid; record then records only the new ones.

Defaults are in the main checkout's target/continuation-r97-goport: the parent
of the git common dir from the main checkout or any worktree, or the main
checkout of lsp_battery_edits.py from an independent clone. A default that is
not there stops the command with the name of its flag. The shared out root is
ls-oracle/effect (traces, golden/<sha12>, results). The default oracle is the
E0 copy in ls-oracle/effect/oracle/<sha12>/bin/tsc (with its BUILD.json), where
<sha12> starts the KNOWN_SHA of scripts/effect/build-oracle.sh. A new E0 goes
in a new oracle/<sha12> dir, and its goldens go in golden/<sha12>.

selfcheck runs E0 16 times by default and then checks the codeAction answers
that hold two actions with one title. effect-tsgo returns these in a random
order (the namespace auto-import fix "Add import from "effect/X"" with and
without the qualified name: 63 requests in e1-t3code). A run that sees the
other order marks the answer multiset, so each run marks each one with chance
1/2: 16 runs leave one of the 63 unmarked in about 1 selfcheck of 1,000, 8 runs
in about 1 of 5. If one is still not marked, selfcheck exits 1: run it again
(runs add up).

check sends every e1 method except initialize. lsp_oracle.py always sends
and compares the initialize request, and check prints it apart from the
other methods (decision D1). effect-tsgo adds "refactor.rewrite" after
"quickfix" in codeActionKinds. Without D1 option B the port does not, so
initialize differs. D1 option B (lane goport-d1b, 535e88364) makes the port
list it as effect-tsgo does, so initialize compares the same here; its
lsp_oracle.py drops that kind from the port's answer only when Go's list
lacks it (the plain Go batteries).

check then compares each hover that lsp_oracle.py classes diff again, with
the "pako:" payload of each Mermaid link (the Layer hover's "Show full
graph" and "Show outline") inflated on both sides: decision D3, tsc-rs
deflates with other bytes than Go's compress/zlib. Only two results can
count as the same; an error or a missing result stays a diff. Nothing else
is normalized, and lsp_oracle.py's results stay as they are. It prints the
hover diffs that remain and writes results/<label>/mermaid-inflate.json.
"""

import argparse
import base64
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import zlib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lsp_battery_edits as be  # noqa: E402

lb = be.lb
BATTERY = "e1"
REPO = Path(__file__).resolve().parents[2]


def main_checkout() -> Path:
    """The checkout whose target dir holds the work data: the parent of the git common dir from the
    main checkout or any worktree. An independent clone has no work data, so it uses the main checkout
    that lsp_battery_edits.py reads the project inputs from."""
    git = subprocess.run(["git", "-C", str(REPO), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                         capture_output=True, text=True)
    main = Path(git.stdout.strip()).parent if git.returncode == 0 else REPO
    return main if (main / "target/continuation-r97-goport").is_dir() else be.REPO


LANES = main_checkout() / "target/continuation-r97-goport"
DEFAULT_OUT_ROOT = LANES / "ls-oracle/effect"
# E0 from scripts/effect/build-oracle.sh; its sha256 is the KNOWN_SHA there and keys the goldens
# (golden/<sha12>). The shared copy is in the out root, under oracle/<sha12>.
DEFAULT_ORACLE = DEFAULT_OUT_ROOT / "oracle/93a772ca8d28/bin/tsc"
DEFAULT_T3CODE = LANES / "effectlsp1/t3code"
T3CODE_COMMIT = "e95b57dc"
LSP_ORACLE = REPO / "scripts/goport/lsp_oracle.py"
SELFCHECK_RUNS = 16

CAPS = {"hover": 8, "yield": 3, "diags": 8, "refactor": 6, "members": 3}

# Files where effect-tsgo 0.51.1 reports Effect diagnostics on T3 Code e95b57dc (tsconfig.json of each
# workspace, --noEmit; effectlsp1/e0/diag), so that the quick fix requests have Effect diagnostics.
T3_EFFECT_FILES = [
    "apps/server/src/assets/AssetAccess.ts", "apps/server/src/auth/ServerSecretStore.ts",
    "apps/server/src/auth/SessionStore.ts", "apps/server/src/checkpointing/Layers/CheckpointDiffQuery.test.ts",
    "apps/server/src/cloud/CliTokenManager.ts", "apps/server/src/cloud/environmentKeys.ts",
    "apps/server/src/cloud/http.ts", "apps/server/src/orchestration/Layers/OrchestrationEngine.test.ts",
    "apps/server/src/orchestration/Layers/ProjectionSnapshotQuery.ts",
    "apps/server/src/orchestration/Layers/ProviderCommandReactor.ts",
    "apps/server/src/orchestration/Layers/ThreadDeletionReactor.ts",
    "apps/server/src/orchestration/commandInvariants.ts", "apps/server/src/persistence/Layers/AuthSessions.ts",
    "apps/server/src/persistence/Layers/ProjectionCheckpoints.ts",
    "apps/server/src/persistence/Layers/ProjectionTurns.ts",
    "apps/server/src/persistence/Layers/ProviderSessionRuntime.ts",
    "apps/server/src/provider/Layers/ClaudeAdapter.test.ts", "apps/server/src/provider/Layers/CodexAdapter.test.ts",
    "apps/server/src/provider/Layers/OpenCodeAdapter.test.ts", "apps/server/src/provider/Layers/OpenCodeAdapter.ts",
    "apps/server/src/provider/Layers/ProviderSessionDirectory.ts", "apps/server/src/provider/acp/AcpSessionRuntime.ts",
    "apps/server/src/relay/AgentAwarenessRelay.test.ts", "apps/server/src/server.test.ts",
    "apps/server/src/serverRuntimeStartup.test.ts", "apps/server/src/serverRuntimeStartup.ts",
    "apps/server/src/sourceControl/BitbucketApi.ts", "apps/server/src/sourceControl/GitLabCli.ts",
    "apps/server/src/sourceControl/SourceControlProviderRegistry.ts",
    "apps/server/src/sourceControl/gitLabMergeRequests.ts",
    "apps/server/src/telemetry/Layers/AnalyticsService.ts", "apps/server/src/terminal/Layers/Manager.ts",
    "apps/server/src/textGeneration/CodexTextGeneration.test.ts",
    "apps/server/src/textGeneration/CodexTextGeneration.ts", "apps/server/src/vcs/GitVcsDriver.ts",
    "apps/server/src/vcs/GitVcsDriverCore.ts", "apps/server/src/ws.ts", "apps/web/src/composerDraftStore.ts",
    "apps/web/src/connection/platform.ts", "apps/web/src/connection/storage.ts",
    "apps/web/src/reviewCommentContext.ts", "packages/client-runtime/src/authorization/tokenStore.ts",
    "packages/client-runtime/src/connection/registry.test.ts",
    "packages/client-runtime/src/connection/resolver.test.ts",
    "packages/client-runtime/src/connection/resolver.ts", "packages/client-runtime/src/connection/supervisor.ts",
    "packages/client-runtime/src/relay/discovery.test.ts", "packages/client-runtime/src/relay/managedRelay.ts",
    "packages/client-runtime/src/relay/managedRelayState.ts", "packages/client-runtime/src/state/session.ts",
    "packages/client-runtime/src/state/shell-sync.test.ts",
    "packages/client-runtime/src/state/threads-sync.test.ts", "packages/shared/src/dpop.test.ts",
    "packages/shared/src/relayClient.ts", "packages/shared/src/relayTracing.ts", "packages/shared/src/schemaJson.ts",
]

INLAY_PREFS = {"inlayHints": {"functionLikeReturnTypes": {"enabled": True}, "variableTypes": {"enabled": True}}}


# ---------------------------------------------------------------------------
# Anchors
# ---------------------------------------------------------------------------


def effect_imports(doc: be.Doc) -> list[dict]:
    """Imports from Effect packages: {start, end, names, ns} (ns: the `* as X` name or None)."""
    out = []
    for s in be.import_statements(doc):
        spec = s["spec"].text.strip("\"'")
        if not (spec == "effect" or spec.startswith("effect/") or spec.startswith("@effect/")):
            continue
        toks = [t for t in doc.toks if s["start"] <= t.start < s["end"]]
        ns = next((toks[i + 2].text for i in range(len(toks) - 2)
                   if toks[i].kind == "*" and toks[i + 1].text == "as" and toks[i + 2].kind == "id"), None)
        out.append({**s, "ns": ns, "specifier": spec})
    return out


def local_names(doc: be.Doc) -> list[str]:
    """Namespace import names (any module: the effect sources import their own modules relatively)
    and the names of `{ X }` imports from Effect packages."""
    names = []
    for s in be.import_statements(doc):
        toks = [t for t in doc.toks if s["start"] <= t.start < s["end"]]
        names.extend(toks[i + 2].text for i in range(len(toks) - 2)
                     if toks[i].kind == "*" and toks[i + 1].text == "as" and toks[i + 2].kind == "id")
    for s in effect_imports(doc):
        if not s["ns"]:
            names.extend(s["names"])
    return names


def decl_names(doc: be.Doc) -> list:
    """Name tokens of `const|let|class|function NAME` declarations at any depth."""
    toks = doc.toks
    return [toks[i + 1] for i in range(len(toks) - 1)
            if toks[i].kind == "id" and toks[i].text in ("const", "let", "class", "function")
            and toks[i + 1].kind == "id" and lb.is_name(toks, i + 1)]


def member_uses(doc: be.Doc, names: list[str]) -> list[tuple]:
    """(X token, . token, member token) for X.member with X an Effect import name."""
    toks, wanted, out = doc.toks, set(names), []
    for i in range(len(toks) - 2):
        if toks[i].kind == "id" and toks[i].text in wanted and toks[i + 1].kind == "." and toks[i + 2].kind == "id":
            if i > 0 and toks[i - 1].kind in (".", "?."):
                continue
            out.append((toks[i], toks[i + 1], toks[i + 2]))
    return out


def call_names(doc: be.Doc) -> list:
    """The last name token of each callee (`a.b.c(` gives c)."""
    toks = doc.toks
    return [toks[i] for i in range(1, len(toks)) if toks[i].kind == "(" and toks[i - 1].kind == "id"
            and lb.is_name(toks, i - 1) and toks[i - 1].text not in ("if", "for", "while", "switch", "catch")]


def yield_stars(doc: be.Doc) -> list[tuple]:
    toks = doc.toks
    return [(toks[i], toks[i + 1]) for i in range(len(toks) - 1)
            if toks[i].kind == "id" and toks[i].text == "yield" and toks[i + 1].kind == "*"]


# ---------------------------------------------------------------------------
# Flows. Each flow leaves the document as it found it.
# ---------------------------------------------------------------------------


def hover(tr, doc: be.Doc, offset: int):
    tr.request("textDocument/hover", doc.tdp(offset))


def flow_hover(tr, doc: be.Doc):
    for t in lb.spread(decl_names(doc), CAPS["hover"]):
        hover(tr, doc, t.start)
    for _, _, m in lb.spread(member_uses(doc, local_names(doc)), CAPS["members"]):
        hover(tr, doc, m.start)
    for y, star in lb.spread(yield_stars(doc), CAPS["yield"]):
        hover(tr, doc, y.start)
        hover(tr, doc, star.start)


def diag_quickfixes(tr, doc: be.Doc, diagnostic: int):
    """For the first diagnostics of the oracle answer (Effect ones on the T3 files): quick fixes only,
    then the lightbulb request. A missing index is not_run on both sides."""
    for i in range(CAPS["diags"]):
        pick = {"event": diagnostic, "pointer": "/items", "pick": {"index": i}}
        for only in (["quickfix"], None):
            ctx = {"diagnostics": [None], "triggerKind": 1}
            if only:
                ctx["only"] = only
            tr.request("textDocument/codeAction", {**doc.td(), "range": None, "context": ctx},
                       {**pick, "into": [{"to": "/range", "from": "/range"}, {"to": "/context/diagnostics/0", "from": ""}]})


def flow_quickfix(tr, doc: be.Doc):
    d = tr.request("textDocument/diagnostic", doc.td())
    diag_quickfixes(tr, doc, d)


def flow_refactor(tr, doc: be.Doc):
    anchors = lb.spread(decl_names(doc), CAPS["refactor"] // 2) + lb.spread(call_names(doc), CAPS["refactor"] // 2)
    for t in anchors:
        tr.request("textDocument/codeAction",
                   {**doc.td(), "range": doc.rng(t.start, t.end), "context": {"diagnostics": [], "triggerKind": 1}})


def appended(tr, doc: be.Doc, text: bytes, at: int, trigger: str | None = None):
    """Append `text` at the end, complete at `at` bytes into it, then remove it."""
    end = len(doc.text)
    doc.change(tr, [(end, end, text)])
    be.completion(tr, doc, end + at, trigger)
    doc.change(tr, [(end, end + len(text), b"")])


def flow_completion(tr, doc: be.Doc):
    names = local_names(doc)
    for _, dot, _ in lb.spread(member_uses(doc, names), CAPS["members"]):
        be.completion(tr, doc, dot.end, ".")
    line = b"\n// @effect-"
    appended(tr, doc, line, len(line))
    cls = b"\nclass __GoportEffect extends "
    appended(tr, doc, cls, len(cls))
    effect = next((s["ns"] or "Effect" for s in effect_imports(doc)
                   if (s["ns"] == "Effect") or (not s["ns"] and "Effect" in s["names"])), None)
    if effect:
        sleep = f'\nvoid {effect}.sleep("10 ")'.encode()
        appended(tr, doc, sleep, len(sleep) - 2)


def flow_comment_extends(tr, doc: be.Doc):
    """The ce requests: Effect's comment items need `@` as the last character (`// @`), and its class
    items need the accessed module (`extends Data.`). FindModuleIdentifier gives "Data" when the file
    has no Data import, so every file gets the Data items."""
    for text, trigger in ((b"\n// @", "@"), (b"\nclass __GoportEffect extends Data.", ".")):
        appended(tr, doc, text, len(text), trigger)


def flow_autoimport(tr, doc: be.Doc):
    imports = effect_imports(doc)
    if not imports:
        return
    s = imports[0]
    name = s["ns"] or (s["names"][0] if s["names"] else None)
    if not name:
        return
    uses = [t for t in doc.toks if t.start >= s["end"] and t.kind == "id" and t.text == name]
    if not uses:
        return
    removed = doc.text[s["start"]:s["end"]]
    use = uses[0]
    doc.change(tr, [(s["start"], s["end"], b"")])
    shift = s["end"] - s["start"]
    d = tr.request("textDocument/diagnostic", doc.td())
    tr.request("textDocument/codeAction",
               {**doc.td(), "range": None, "context": {"diagnostics": [None], "only": ["quickfix"], "triggerKind": 1}},
               {"event": d, "pointer": "/items", "pick": {"match": {"message": f"Cannot find name '{name}'."}},
                "into": [{"to": "/range", "from": "/range"}, {"to": "/context/diagnostics/0", "from": ""}]})
    ev = tr.request("textDocument/completion",
                    {**doc.tdp(use.end - shift), "context": {"triggerKind": 1}})
    tr.request("completionItem/resolve", params_from={"event": ev, "pointer": "/items", "pick": {"match": {"label": name}}})
    doc.change(tr, [(s["start"], s["start"], removed)])


def flow_symbols_inlay(tr, doc: be.Doc):
    tr.request("textDocument/documentSymbol", doc.td())
    be.configure(tr, INLAY_PREFS)
    tr.request("textDocument/inlayHint", {**doc.td(), "range": doc.full()})
    be.configure(tr, None)


FLOWS = (flow_hover, flow_quickfix, flow_refactor, flow_completion, flow_autoimport, flow_symbols_inlay)
CE_FLOWS = (flow_comment_extends,)


def file_trace(rel: str, text: bytes, flows) -> "lb.Trace":
    tr = lb.Trace()
    tr.request("initialize", be.initialize_params(be.UTF16))
    doc = be.Doc(rel, text, be.UTF16)
    doc.open(tr)
    for flow in flows:
        flow(tr, doc)
    assert doc.text == text, rel
    return tr


# ---------------------------------------------------------------------------
# Parts
# ---------------------------------------------------------------------------


def effect_files(_args) -> tuple[Path, list[str]]:
    root = be.INPUTS / "effect/source/packages/effect"
    rels = lb.list_sources(root, ["src/*"], [], [".ts"])
    if len(rels) != 457:
        raise SystemExit(f"e1-effect: found {len(rels)} files, expected 457")
    return root, rels[::8]


def t3code_files(args) -> tuple[Path, list[str]]:
    root = Path(args.t3code).resolve()
    if not root.is_dir():
        raise SystemExit(f"e1-t3code: no T3 Code copy at {root}; pass --t3code DIR (T3 Code at {T3CODE_COMMIT})")
    head = subprocess.run(["git", "-C", str(root), "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True)
    if head.stdout.strip() != T3CODE_COMMIT:
        raise SystemExit(f"e1-t3code: {root} is at {head.stdout.strip() or '?'}, expected {T3CODE_COMMIT}")
    picked = set()
    for ws in ("apps/server", "packages/client-runtime", "packages/shared"):
        picked.update(f"{ws}/{r}" for r in lb.list_sources(root / ws, ["src/*"], [], [".ts"])[::12])
    missing = [r for r in T3_EFFECT_FILES if not (root / r).is_file()]
    if missing:
        raise SystemExit(f"e1-t3code: missing {missing[:3]}")
    picked.update(T3_EFFECT_FILES)
    return root, sorted(picked)


# part name: (files, flows)
PARTS = {f"{BATTERY}-effect": (effect_files, FLOWS), f"{BATTERY}-t3code": (t3code_files, FLOWS),
         f"{BATTERY}-effect-ce": (effect_files, CE_FLOWS), f"{BATTERY}-t3code-ce": (t3code_files, CE_FLOWS)}


def cmd_build(args) -> int:
    traces = Path(args.out_root) / "traces"
    names = args.parts.split(",") if args.parts else list(PARTS)
    index = {"format": "goport-lsp-battery-index/1", "battery": BATTERY,
             "generatorSha256": lb.file_sha(Path(__file__)), "editsSha256": lb.file_sha(Path(be.__file__)),
             "lspBatterySha256": lb.file_sha(be.LSP_BATTERY_PY), "parts": []}
    for name in names:
        if name not in PARTS:
            raise SystemExit(f"unknown part {name}; parts: {', '.join(PARTS)}")
        files, flows = PARTS[name]
        root, rels = files(args)
        lb.guard_out(traces, [root, be.INPUTS])
        entries = []
        for rel in rels:
            text = lb.read_source(root / rel)
            tr = file_trace(rel, text, flows)
            src = {"kind": "effect", "part": name, "file": rel, "complete": True,
                   "sha256": hashlib.sha256(text).hexdigest()}
            header = be.header(f"{name}/{rel}", src, {"kind": "project", "dir": str(root)}, be.UTF16)
            entries.append(lb.write_trace(traces, header, tr))
        index["parts"].append({"name": name, "kind": "effect", "schedule": "manual", "traces": entries})
    index["traceSetSha256"] = hashlib.sha256("".join(
        f"{t['name']} {t['sha256']}\n" for p in index["parts"] for t in p["traces"]).encode()).hexdigest()
    traces.mkdir(parents=True, exist_ok=True)
    (traces / f"{BATTERY}.index.json").write_text(json.dumps(index, indent=1) + "\n")
    lb.print_summary(index["parts"])
    return 0


# ---------------------------------------------------------------------------
# lsp_oracle.py wrapper
# ---------------------------------------------------------------------------


def trace_methods(out_root: Path) -> list[str]:
    methods = set()
    for path in sorted((out_root / "traces").glob(f"{BATTERY}-*/**/*.jsonl")):
        with open(path, encoding="utf-8") as f:
            next(f)
            for line in f:
                ev = json.loads(line)
                if ev.get("kind") == "request":
                    methods.add(ev["method"])
    return sorted(methods - {"initialize"})


def oracle(cmd: str, args, extra: list[str]) -> int:
    if not Path(args.oracle).is_file():
        raise SystemExit(f"no E0 oracle at {args.oracle}; build it with scripts/effect/build-oracle.sh "
                         "and pass --oracle BIN")
    if not (Path(args.out_root) / "traces" / f"{BATTERY}.index.json").is_file():
        raise SystemExit(f"no e1 traces in {args.out_root}/traces; run build, or pass --out-root R")
    argv = [sys.executable, str(LSP_ORACLE), cmd, "--out-root", str(args.out_root), "--battery", args.parts or BATTERY,
            "--oracle", str(args.oracle), "--jobs", str(args.jobs)]
    if args.only:
        argv += ["--only", args.only]
    return subprocess.run(argv + extra).returncode


def same_title_unmarked(args) -> tuple[int, list[str]]:
    """Counts the codeAction answers in the goldens with two actions of one title, and lists the ones
    that selfcheck has not marked multiset at the top array (pattern "") or unstable."""
    groot = Path(args.out_root) / "golden" / lb.file_sha(Path(args.oracle))[:12]
    parts = args.parts.split(",") if args.parts else None
    total, unmarked = 0, []
    for gpath in sorted(groot.glob(f"{BATTERY}-*/**/*.golden.jsonl.gz")):
        name = str(gpath.relative_to(groot)).removesuffix(".golden.jsonl.gz")
        if parts and name.split("/", 1)[0] not in parts:
            continue
        if args.only and args.only not in name.split("/", 1)[1]:
            continue
        fpath = gpath.with_name(gpath.name.removesuffix(".golden.jsonl.gz") + ".flaky.json")
        flaky = json.loads(fpath.read_text()) if fpath.is_file() else {}
        events = flaky.get("events", {}) if flaky.get("goldenSha256") == lb.file_sha(gpath) else {}
        with gzip.open(gpath, "rt", encoding="utf-8") as f:
            next(f)
            for line in f:
                rec = json.loads(line)
                if rec.get("kind") != "request" or rec.get("method") != "textDocument/codeAction" or rec.get("status") != "ok":
                    continue
                titles = [a.get("title") for a in rec["response"].get("result") or []]
                if len(titles) == len(set(titles)):
                    continue
                total += 1
                ev = events.get(str(rec["i"]), {})
                if "" not in ev.get("multiset", []) and not ev.get("unstable"):
                    unmarked.append(f"{name} event {rec['i']}")
    return total, unmarked


def cmd_selfcheck(args) -> int:
    rc = oracle("selfcheck", args, ["--runs", str(args.runs)])
    total, unmarked = same_title_unmarked(args)
    print(f"\ncodeAction answers with two actions of one title: {total}, not marked multiset: {len(unmarked)}")
    if unmarked:
        print("\n".join(f"  {u}" for u in unmarked))
        print("run selfcheck again (runs add up). If Go keeps one order for a request, check it by hand.")
        return rc or 1
    return rc


MERMAID_PAKO = re.compile(r"pako:([A-Za-z0-9_-]+)")


def canon(v) -> str:
    """lsp_oracle.py canon: the JSON text that its compare uses."""
    return json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def inflate_mermaid(v):
    """v with the "pako:<base64url>" payload of each Mermaid link in its strings inflated (decision D3)."""
    if isinstance(v, str):
        def one(m):
            raw = base64.urlsafe_b64decode(m.group(1) + "=" * (-len(m.group(1)) % 4))
            return "pako:<" + zlib.decompress(raw).decode("utf-8") + ">"
        return MERMAID_PAKO.sub(one, v)
    if isinstance(v, list):
        return [inflate_mermaid(x) for x in v]
    if isinstance(v, dict):
        return {k: inflate_mermaid(x) for k, x in v.items()}
    return v


def mermaid_recheck(out_root: Path, label: str) -> tuple[int, list[dict]]:
    """Compares each hover diff of the label again with the Mermaid payloads inflated on both sides.
    Returns the number of hover diffs and the rows of those that still differ; writes all rows to
    results/<label>/mermaid-inflate.json."""
    rdir = out_root / "results" / label
    rows = []
    for tpath in sorted((rdir / "traces").glob("**/*.json")):
        tr = json.loads(tpath.read_text())
        diffs = [ev for ev in tr["events"] if ev["method"] == "textDocument/hover" and ev["class"] == "diff"]
        if not diffs:
            continue
        with gzip.open(tr["golden"], "rt", encoding="utf-8") as f:
            next(f)
            golden = {r["i"]: r for r in map(json.loads, f) if r.get("kind") == "request"}
        with gzip.open(tr["responses"], "rt", encoding="utf-8") as f:
            responses = {r["i"]: r for r in map(json.loads, f)}
        for ev in diffs:
            g = golden[ev["i"]]["response"]
            r = responses[ev["i"]]["response"]
            # Only two results can be the same: an error or a missing result on either side stays a diff
            # (both would read as None).
            same = ("result" in g and "result" in r
                    and canon(inflate_mermaid(g["result"])) == canon(inflate_mermaid(r["result"])))
            rows.append({"battery": tr["battery"], "trace": tr["trace"], "i": ev["i"],
                         "mermaid": "pako:" in canon(g) or "pako:" in canon(r),
                         "class": "same" if same else "diff"})
    (rdir / "mermaid-inflate.json").write_text(json.dumps({"label": label, "rows": rows}, indent=1) + "\n")
    return len(rows), [row for row in rows if row["class"] == "diff"]


def cmd_check(args) -> int:
    methods = trace_methods(Path(args.out_root))
    rc = oracle("check", args, ["--goport", args.server, "--label", args.label, "--methods", ",".join(methods)])
    summary = Path(args.out_root) / "results" / args.label / "summary.json"
    if not summary.is_file():
        return rc or 1
    s = json.loads(summary.read_text())
    by_method = s.get("methods", {})
    init = by_method.pop("initialize", {})
    print(f"\ninitialize (D1 refactor.rewrite; same with D1 option B): {init}")
    total = {}
    for m, c in sorted(by_method.items()):
        print(f"{m:40s} {json.dumps(c, sort_keys=True)}")
        for k, v in c.items():
            total[k] = total.get(k, 0) + v
    print(f"{'all but initialize':40s} {json.dumps(total, sort_keys=True)}")
    print(f"summary: {summary}")
    hover_diffs, still = mermaid_recheck(Path(args.out_root), args.label)
    print(f"\nhover diffs: {hover_diffs}; after Mermaid inflate (D3): {hover_diffs - len(still)} same, "
          f"{len(still)} diff")
    for row in still:
        print(f"  {row['battery']}/{row['trace']} event {row['i']}")
    print(f"rows: {Path(args.out_root) / 'results' / args.label / 'mermaid-inflate.json'}")
    return rc


def main() -> int:
    if sys.argv[1:2] == ["help"]:
        print(__doc__)
        return 0
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p, oracle_args=True):
        p.add_argument("--out-root", default=str(DEFAULT_OUT_ROOT), help=f"default {DEFAULT_OUT_ROOT}")
        if oracle_args:
            p.add_argument("--oracle", default=str(DEFAULT_ORACLE), help="the E0 oracle (scripts/effect/build-oracle.sh)")
            p.add_argument("--parts", help="comma list of parts (default: all)")
            p.add_argument("--jobs", type=int, default=4)
            p.add_argument("--only", help="only traces whose name contains this text")

    b = sub.add_parser("build", help="write the e1 traces")
    common(b, oracle_args=False)
    b.add_argument("--parts", help="comma list of parts (default: all)")
    b.add_argument("--t3code", default=str(DEFAULT_T3CODE), help=f"T3 Code copy at {T3CODE_COMMIT}")
    r = sub.add_parser("record", help="lsp_oracle.py record with the E0 oracle")
    common(r)
    r.add_argument("--force", action="store_true")
    sc = sub.add_parser("selfcheck", help="lsp_oracle.py selfcheck with the E0 oracle")
    common(sc)
    sc.add_argument("--runs", type=int, default=SELFCHECK_RUNS, help=f"default {SELFCHECK_RUNS}")
    c = sub.add_parser("check", help="lsp_oracle.py check of a server against the E0 goldens")
    common(c)
    c.add_argument("--server", required=True, help="server under test (tsc-rs tsgo)")
    c.add_argument("--label", required=True)
    sub.add_parser("list", help="print the part names")
    args = ap.parse_args()
    if args.cmd == "list":
        print("\n".join(PARTS))
        return 0
    if args.cmd == "build":
        return cmd_build(args)
    if args.cmd == "record":
        return oracle("record", args, ["--force"] if args.force else [])
    if args.cmd == "selfcheck":
        return cmd_selfcheck(args)
    return cmd_check(args)


if __name__ == "__main__":
    sys.exit(main())
