#!/usr/bin/env python3
"""Port Go integer const blocks (flags and enums) to Rust newtypes, 1:1.

Usage: genflags.py <go-internal-dir> <out.rs>
Each Go `type X uintN|intN` with const blocks becomes `pub struct X(pub T)`
with associated consts named in SCREAMING_SNAKE (prefix `X` stripped).
"""
import re, sys, os

GO = sys.argv[1]
OUT = sys.argv[2]

FILES = [
    "ast/checkflags.go", "ast/flow.go", "ast/functionflags.go", "ast/modifierflags.go",
    "ast/nodeflags.go", "ast/subtreefacts.go", "ast/symbolflags.go", "ast/tokenflags.go",
    "ast/utilities.go", "ast/ast.go", "ast/precedence.go",
    "binder/binder.go",
    "checker/checker.go", "checker/types.go", "checker/relater.go", "checker/jsx.go",
    "checker/mapper.go", "checker/utilities.go", "checker/inference.go", "checker/flow.go",
    "checker/grammarchecks.go", "checker/nodebuilderimpl.go", "checker/emitresolver.go",
    "checker/symbolaccessibility.go", "checker/services.go", "checker/printer.go",
    "core/compileroptions.go", "core/languagevariant.go", "core/scriptkind.go", "core/tristate.go",
]

RUST_T = {"uint8": "u8", "uint16": "u16", "uint32": "u32", "uint64": "u64", "uint": "u64",
          "int8": "i8", "int16": "i16", "int32": "i32", "int64": "i64", "int": "i64"}

# Types to skip: Kind is covered by ts_ast::SyntaxKind; internal/unhelpful ones.
SKIP = {"Kind", "TextPos", "symbolTableID"}

def snake(name):
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", s)
    return s.upper()

types = {}   # name -> rust int type
order = []
consts = {}  # type -> list of (goname, expr_str)
allconst = {}  # goname -> (type, value)

def eval_expr(expr, iota, tname):
    e = expr.strip()
    e = re.sub(r"//.*", "", e).strip()
    if not e:
        return None
    # replace Go identifiers with values
    def rep(m):
        w = m.group(0)
        if w == "iota":
            return str(iota)
        if w in allconst:
            return str(allconst[w][1])
        if re.fullmatch(r"[A-Z][A-Za-z0-9]*", w) and w in types:
            return ""  # type conversion like TypeFlags(1)
        raise KeyError(w)
    py = re.sub(r"[A-Za-z_][A-Za-z0-9_]*", rep, e)
    py = py.replace("&^", "& ~")
    py = re.sub(r"(^|[(&|+\-*~<>]\s*)\^", r"\1~", py)
    return int(eval(py, {}, {}))

src_all = {}
pending = []
for f in FILES:
    p = os.path.join(GO, f)
    if not os.path.exists(p):
        continue
    src = open(p).read()
    src_all[f] = src
    for m in re.finditer(r"^type ([A-Za-z][A-Za-z0-9]*) (u?int(?:8|16|32|64)?)$", src, re.M):
        n = m.group(1)
        if n in SKIP:
            continue
        types[n] = RUST_T[m.group(2)]

for f, src in src_all.items():
    for block in re.finditer(r"^const \($(.*?)^\)$", src, re.M | re.S):
        body = block.group(1)
        iota = 0
        cur_t = None
        cur_expr = None
        for line in body.split("\n"):
            raw = line
            line = re.sub(r"//.*", "", line).strip()
            if not line:
                continue
            m = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)(?:\s+([A-Za-z][A-Za-z0-9]*))?(?:\s*=\s*(.+))?", line)
            if not m:
                iota += 1
                continue
            name, t, expr = m.group(1), m.group(2), m.group(3)
            if expr is not None:
                cur_t = t
                cur_expr = expr
                if t is None:
                    # Untyped const: infer from referenced consts or the name prefix.
                    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", re.sub(r"//.*", "", expr)):
                        if w in allconst:
                            cur_t = allconst[w][0]
                            break
                    if cur_t is None:
                        for tn in sorted(types, key=len, reverse=True):
                            if name.startswith(tn):
                                cur_t = tn
                                break
            elif t is not None:
                # typed with no value: not valid Go const continuation, skip
                iota += 1
                continue
            if cur_t in types and name != "_":
                pending.append((f, name, cur_t, cur_expr, iota))
                consts.setdefault(cur_t, []).append(name)
                if cur_t not in order:
                    order.append(cur_t)
            iota += 1

# Resolve with repeated passes so forward references work.
for _ in range(10):
    left = []
    for (f, name, t, expr, iota) in pending:
        try:
            allconst[name] = (t, eval_expr(expr, iota, t))
        except KeyError:
            left.append((f, name, t, expr, iota))
    pending = left
for (f, name, t, expr, iota) in pending:
    print(f"warn: {f}: {name} = {expr} unresolved", file=sys.stderr)
    consts[t].remove(name)
consts = {t: [(n, allconst[n][1]) for n in ns] for t, ns in consts.items()}

def mask(rt):
    bits = int(rt[1:])
    return (1 << bits) - 1

out = []
out.append("// Code generated by /home/theo/Code/sandbox/ts-rust/scripts/goport/genflags.py from pinned typescript-go\n"
           "// dc37b5249ab60e2bbce936f71b883e6c8136167e. DO NOT EDIT.\n"
           "#![allow(clippy::unreadable_literal, clippy::cast_possible_wrap, dead_code)]\n\n"
           "use crate::flags_macros::{go_flags, go_enum};\n")
for t in order:
    rt = types[t]
    items = consts[t]
    is_flags = t.endswith("Flags") or t.endswith("Facts") or t in {
        "CheckMode", "IterationUse", "TypeFacts", "IntersectionState", "RecursionFlags",
        "RelationComparisonResult", "SignatureCheckMode", "ExternalEmitHelpers",
        "MappedTypeModifiers", "OuterExpressionKinds", "SemanticMeaning", "InferencePriority",
        "DeclarationMeaning", "PredicateSemantics", "UnusedKind", "IntersectionFlags",
        "ContainerFlags", "PragmaKindFlags", "OperatorPrecedenceFlags", "MinArgumentCountFlags"}
    macro = "go_flags" if is_flags else "go_enum"
    out.append(f"{macro}!({t}, {rt} {{")
    seen = set()
    for name, v in items:
        short = name[len(t):] if name.startswith(t) and len(name) > len(t) else name
        rn = snake(short)
        if rn[0].isdigit():
            rn = "_" + rn
        if rn in seen:
            rn = snake(name)
        seen.add(rn)
        if rt.startswith("u"):
            v &= mask(rt)
            lit = f"0x{v:x}" if v > 9 else str(v)
        else:
            lit = str(v)
        out.append(f"    {rn} = {lit}; // {name}")
    out.append("});\n")

open(OUT, "w").write("\n".join(out))
print(f"{len(order)} types, {sum(len(consts[t]) for t in order)} consts", file=sys.stderr)
missing = sorted(set(types) - set(order))
print("types without consts:", missing, file=sys.stderr)
