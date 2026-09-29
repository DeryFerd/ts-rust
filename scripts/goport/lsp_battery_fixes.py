#!/usr/bin/env python3
"""Code action battery b5 for the LSP parity oracle (trace format goport-lsp-trace/1).

The b1 and b2 sweeps ask for a quick fix at diagnostic index 0..19 of each
file. The project files have no errors, so most of those requests find no
diagnostic and are `not_run` (8,573 of 9,879 codeAction requests at R136).
This battery makes the errors first, so each quick fix request has a
diagnostic. The pinned Go has three fix providers (ls/codeactions.go):
import fixes, isolatedDeclarations fixes and "class incorrectly implements
interface". The project configs do not set isolatedDeclarations, so b5
covers the other two, on every file:

  imports     remove each named import statement in turn (up to a cap), then
              one quick fix per removed name (the diagnostic picked by its
              "Cannot find name 'X'." message), a codeAction with all
              diagnostics over the whole file, and source.fixAll
  exports     use names that other project files export and this file does
              not mention (up to a cap), then a quick fix for that name and
              source.fixAll
  implements  a class that implements an interface of this file with no
              members, then a quick fix for TS2420

Each edit is undone before the next one, so each flow starts from the file
text. Project roots are only read: edits are didChange overlays.

Usage:
  lsp_battery_fixes.py build --out TRACES [--parts b5-query-core,b5-effect,...]
  lsp_battery_fixes.py list

build writes <TRACES>/<part>/<file>.jsonl and <TRACES>/b5.index.json. Run them
with scripts/goport/lsp_oracle.py (`--battery b5`). The Doc class, the anchors
and the project list come from lsp_battery_edits.py (b4).
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lsp_battery_edits as be  # noqa: E402

lb = be.lb
BATTERY = "b5"

# Per-file caps. Effect files are large and each diagnostic request checks the
# file again, so effect gets smaller caps and a sample of its files.
CAPS = {"imports": 8, "names": 6, "exports": 4, "interfaces": 2}
EFFECT_CAPS = {"imports": 4, "names": 4, "exports": 2, "interfaces": 1}

PROJECTS = [
    *({**p, "caps": CAPS} for p in be.PROJECTS),
    # Every 8th file of the b3-effect include, as tests2/lsp b3s-effect and b3z-effect.
    {"name": "effect", "root": be.INPUTS / "effect/source/packages/effect", "include": ["src/*"],
     "exclude": [], "expectFiles": 457, "every": 8, "caps": EFFECT_CAPS},
]


def quickfix_for(tr, doc: be.Doc, diagnostic: int, match: dict):
    """A quick fix for the first diagnostic of event `diagnostic` whose fields equal `match`."""
    tr.request("textDocument/codeAction",
               {**doc.td(), "range": None,
                "context": {"diagnostics": [None], "only": ["quickfix"], "triggerKind": 1}},
               {"event": diagnostic, "pointer": "/items", "pick": {"match": match},
                "into": [{"to": "/range", "from": "/range"}, {"to": "/context/diagnostics/0", "from": ""}]})


def flow_imports(tr, doc: be.Doc, caps: dict):
    named = [s for s in be.import_statements(doc) if s["names"]]
    for s in be.spread(named, caps["imports"]):
        removed = doc.text[s["start"]:s["end"]]
        doc.change(tr, [(s["start"], s["end"], b"")])
        d = tr.request("textDocument/diagnostic", doc.td())
        for name in s["names"][:caps["names"]]:
            quickfix_for(tr, doc, d, {"message": f"Cannot find name '{name}'."})
        be.all_diagnostics_action(tr, doc, d)
        be.source_action(tr, doc, ["source.fixAll"])
        doc.change(tr, [(s["start"], s["start"], removed)])


def missing_exports(doc: be.Doc, exports: dict, cap: int) -> list[tuple[str, str]]:
    """Names that other project files export and this file never mentions, spread over the list."""
    present = {t.text for t in doc.toks if t.kind == "id"}
    cands = sorted({(n, k) for rel, names in exports.items() if rel != doc.rel for n, k in names
                    if n not in present})
    if not cands:
        return []
    # Start at a place that depends on the file, as b4 pick_missing_export does.
    start = int(hashlib.sha256(doc.rel.encode()).hexdigest(), 16) % len(cands)
    return be.spread(cands[start:] + cands[:start], cap)


def flow_exports(tr, doc: be.Doc, exports: dict, caps: dict):
    for name, kind in missing_exports(doc, exports, caps["exports"]):
        line = (b"\nvoid " + name.encode() + b";\n") if kind == "value" \
            else (b"\ntype __GoportFix = " + name.encode() + b";\n")
        end = len(doc.text)
        doc.change(tr, [(end, end, line)])
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfix_for(tr, doc, d, {"message": f"Cannot find name '{name}'."})
        be.source_action(tr, doc, ["source.fixAll"])
        doc.change(tr, [(end, end + len(line), b"")])


def flow_implements(tr, doc: be.Doc, caps: dict):
    for name, count in be.interfaces(doc)[:caps["interfaces"]]:
        args = b"<" + b", ".join([b"any"] * count) + b">" if count else b""
        cls = b"\nclass __GoportImpl implements " + name.encode() + args + b" {}\n"
        end = len(doc.text)
        doc.change(tr, [(end, end, cls)])
        d = tr.request("textDocument/diagnostic", doc.td())
        quickfix_for(tr, doc, d, {"code": 2420})
        doc.change(tr, [(end, end + len(cls), b"")])


def project_part(project: dict, out_dir: Path) -> list[dict]:
    root = project["root"]
    rels = lb.list_sources(root, project["include"], project["exclude"], be.manifest()["sweep"]["extensions"])
    if len(rels) != project["expectFiles"]:
        raise SystemExit(f"{project['name']}: found {len(rels)} files, expected {project['expectFiles']}")
    texts = {rel: lb.read_source(root / rel) for rel in rels}
    exports = {rel: be.exported_names(be.Doc(rel, text, be.UTF16)) for rel, text in texts.items()}
    part = f"{BATTERY}-{project['name']}"
    entries = []
    for rel in rels[::project.get("every", 1)]:
        text = texts[rel]
        tr = lb.Trace()
        tr.request("initialize", be.initialize_params(be.UTF16))
        doc = be.Doc(rel, text, be.UTF16)
        doc.open(tr)
        tr.request("textDocument/diagnostic", doc.td())
        flow_imports(tr, doc, project["caps"])
        flow_exports(tr, doc, exports, project["caps"])
        flow_implements(tr, doc, project["caps"])
        assert doc.text == text, rel
        src = {"kind": "fixes", "part": part, "file": rel, "complete": True,
               "sha256": hashlib.sha256(text).hexdigest()}
        header = be.header(f"{part}/{rel}", src, {"kind": "project", "dir": str(root.resolve())}, be.UTF16)
        entries.append(lb.write_trace(out_dir, header, tr))
    return entries


PARTS = {f"{BATTERY}-{p['name']}": (lambda out, p=p: project_part(p, out)) for p in PROJECTS}


def cmd_build(args) -> int:
    out_dir = Path(args.out)
    lb.guard_out(out_dir, [p["root"] for p in PROJECTS] + [be.INPUTS, lb.BATTERY_DIR])
    names = args.parts.split(",") if args.parts else list(PARTS)
    index = {"format": "goport-lsp-battery-index/1", "battery": BATTERY,
             "generatorSha256": lb.file_sha(Path(__file__)),
             "editsSha256": lb.file_sha(Path(be.__file__)),
             "lspBatterySha256": lb.file_sha(be.LSP_BATTERY_PY), "parts": []}
    for name in names:
        if name not in PARTS:
            raise SystemExit(f"unknown part {name}; parts: {', '.join(PARTS)}")
        traces = PARTS[name](out_dir)
        index["parts"].append({"name": name, "kind": "fixes", "schedule": "manual", "traces": traces})
    index["traceSetSha256"] = hashlib.sha256("".join(
        f"{t['name']} {t['sha256']}\n" for p in index["parts"] for t in p["traces"]).encode()).hexdigest()
    (out_dir / f"{BATTERY}.index.json").write_text(json.dumps(index, indent=1) + "\n")
    lb.print_summary(index["parts"])
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build", help="write the code action traces")
    b.add_argument("--out", required=True, help="traces root")
    b.add_argument("--parts", help="comma list of parts (default: all)")
    sub.add_parser("list", help="print the part names")
    args = ap.parse_args()
    if args.cmd == "list":
        print("\n".join(PARTS))
        return 0
    return cmd_build(args)


if __name__ == "__main__":
    sys.exit(main())
