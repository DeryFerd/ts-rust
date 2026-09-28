#!/usr/bin/env python3
"""Markdown table of buildbench.sh results.

usage: buildbench-report.py <runs-dir>...

Reads every <runs-dir>/results.tsv and the cargo timing pages in <runs-dir>/logs/. One row per
cell (label without its -rN suffix); each value column lists the runs as "a / b". "lib" is the
ts_goport lib unit time, "front" its time to metadata (the frontend part, before codegen).
"""
import csv
import json
import re
import sys
from collections import OrderedDict
from pathlib import Path


def lib_times(html: Path):
    try:
        text = html.read_text()
        units = json.loads(re.search(r"const UNIT_DATA = (\[.*?\]);\n", text, re.S).group(1))
    except (OSError, AttributeError, ValueError):
        return None, None
    for u in units:
        if u["name"] == "ts_goport" and u["target"].strip() in ("", "lib"):
            # Stable cargo gives rmeta_time; newer cargo gives a "frontend" section instead.
            front = u.get("rmeta_time")
            for name, span in u.get("sections") or []:
                if name == "frontend":
                    front = span["end"] - span["start"]
            return u["duration"], front
    return None, None


def fmt(values, unit=""):
    return " / ".join("-" if v is None else f"{v:.0f}{unit}" for v in values)


cells = OrderedDict()
for d in map(Path, sys.argv[1:]):
    tsv = d / "results.tsv"
    if not tsv.exists():
        continue
    for row in csv.DictReader(tsv.open(), delimiter="\t"):
        cell = re.sub(r"-r\d+$", "", row["label"])
        lib, front = lib_times(d / "logs" / f"{row['label']}.html")
        cells.setdefault(cell, []).append((row, lib, front))

print("| cell | toolchain | profile | RUSTFLAGS | incr | runs | wall s | user s | sys s | max RSS GiB | lib s | front s | rc |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for cell, runs in cells.items():
    r0 = runs[0][0]
    print(
        f"| {cell} | {r0['toolchain']} | {r0['profile']} | {r0['rustflags']} | {r0['incr']} | {len(runs)} | "
        f"{fmt(float(r['wall_s']) for r, _, _ in runs)} | {fmt(float(r['user_s']) for r, _, _ in runs)} | "
        f"{fmt(float(r['sys_s']) for r, _, _ in runs)} | "
        + " / ".join(f"{int(r['maxrss_kib']) / 1048576:.1f}" for r, _, _ in runs)
        + f" | {fmt(l for _, l, _ in runs)} | {fmt(f for _, _, f in runs)} | "
        + ",".join(r["rc"] for r, _, _ in runs)
        + " |"
    )
