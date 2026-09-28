#!/bin/bash
# usage: np-suite.sh run <label> <tsgo-bin>     run the suite with one binary
#        np-suite.sh diff <labelA> <labelB>     per-test status changes from A to B
# Runs the typescript-go native-preview API client suite (_packages/native-preview:
# test/**/*.test.ts, sync and async api.test.ts, astnav, ast, encoder, wtf8,
# compilerOptions) against any tsgo binary.
# It copies the package, and the repo files that the tests read, into a new tree where
# built/local/tsgo is a symlink to the binary. The package then spawns that binary
# (lib/getExePath.js). Copies use reflink on btrfs, so they are cheap.
# The Go checkout is NP_GO_DIR (default: the pin 52168999f3dc checkout). Node >= 22.
# NP_KEEP=1 keeps the tree. NP_TEST_TIMEOUT (ms, default 300000) limits each test.
# Output: target/continuation-r97-goport/compat-backlog/np-suite/<label>/
#   results.jsonl  one line per test and suite: file, name ("a > b"), kind, status, msg
#   spec.log       the normal node:test output
#   summary.txt    counts by status
#   meta.txt       binary and sha256, Go commit, node, host, node exit code
set -uo pipefail
cd /home/theo/Code/sandbox/ts-rust
OUT=target/continuation-r97-goport/compat-backlog/np-suite
GO=${NP_GO_DIR:-$HOME/.explore/repos/microsoft__typescript-go@52168999f}
usage() { sed -n '2,16p' "$0"; exit 2; }

run() {
  local label=$1 bin
  bin=$(realpath "$2") || exit 2
  [[ -x $bin ]] || { echo "not executable: $bin" >&2; exit 2; }
  local o=$OUT/$label
  rm -rf "$o"; mkdir -p "$o"; o=$(realpath "$o")
  t=$(mktemp -d "${TMPDIR:-/tmp}/np-suite.XXXXXX")
  [[ ${NP_KEEP:-0} == 1 ]] && echo "tree $t (kept)" || trap 'rm -rf "$t"' EXIT
  mkdir -p "$t/_packages" "$t/built/local" "$t/internal/core" "$t/_submodules/TypeScript" "$t/testdata/baselines/reference"
  cp -a --reflink=auto "$GO/_packages/native-preview" "$t/_packages/"
  cp -a --reflink=auto "$GO/internal/core/compileroptions.go" "$t/internal/core/"
  cp -a --reflink=auto "$GO/testdata/baselines/reference/astnav" "$t/testdata/baselines/reference/"
  # The TypeScript submodule without its 570 MB tests dir. The tests read only src.
  for f in "$GO"/_submodules/TypeScript/*; do
    [[ $(basename "$f") == tests ]] || cp -a --reflink=auto "$f" "$t/_submodules/TypeScript/"
  done
  # api.test.ts imports api.bench.ts, which needs tinybench and typescript. Read only.
  ln -s "$GO/node_modules" "$t/node_modules"
  ln -s "$bin" "$t/built/local/tsgo"
  { echo "bin $bin"; echo "sha256 $(sha256sum "$bin" | cut -d' ' -f1)"; echo "go $GO $(git -C "$GO" rev-parse HEAD)"; echo "node $(node --version)"; echo "host $(hostname)"; date -Is; } > "$o/meta.txt"

  # Reporter: one JSON line per finished test or suite, with its full name path.
  # test:start and test:pass/fail come in definition order per file, so a stack
  # per file gives the parent names.
  cat > "$t/reporter.mjs" <<'EOF'
import path from "node:path";
export default async function* (source) {
  const stacks = new Map();
  const base = process.cwd();
  for await (const { type, data } of source) {
    if (type === "test:start") {
      const s = stacks.get(data.file) ?? [];
      s.length = data.nesting;
      s.push(data.name);
      stacks.set(data.file, s);
    } else if (type === "test:pass" || type === "test:fail") {
      const names = [...(stacks.get(data.file) ?? []).slice(0, data.nesting), data.name];
      let status = type === "test:pass" ? "pass" : "fail";
      if (data.skip !== undefined) status = "skip";
      if (data.todo !== undefined) status = "todo";
      const err = data.details?.error;
      const cause = err?.cause ?? err;
      yield JSON.stringify({
        file: data.file ? path.relative(base, data.file) : null,
        name: names.join(" > "),
        kind: data.details?.type ?? "test",
        status,
        ms: Math.round(data.details?.duration_ms ?? 0),
        failureType: err?.failureType,
        msg: cause ? String(cause.message ?? cause).slice(0, 4000) : undefined,
      }) + "\n";
    }
  }
}
EOF
  echo "np-suite $label: running with $bin"
  ( cd "$t/_packages/native-preview" && timeout "${NP_TIMEOUT:-1800}" node --experimental-strip-types --no-warnings \
      --conditions @typescript/source --test --test-timeout="${NP_TEST_TIMEOUT:-300000}" \
      --test-reporter=spec --test-reporter-destination="$o/spec.log" \
      --test-reporter="$t/reporter.mjs" --test-reporter-destination="$o/results.jsonl" \
      './test/**/*.test.ts' )
  local rc=$?
  echo "rc $rc" >> "$o/meta.txt"
  node -e '
    const rows = require("fs").readFileSync(process.argv[1], "utf8").trim().split("\n").filter(Boolean).map(JSON.parse);
    const tests = rows.filter(r => r.kind === "test"), n = {};
    for (const r of tests) n[r.status] = (n[r.status] ?? 0) + 1;
    console.log(`tests ${tests.length}`, JSON.stringify(n), `failed suites ${rows.filter(r => r.kind === "suite" && r.status === "fail").length}`);
  ' "$o/results.jsonl" | tee "$o/summary.txt"
  echo "node rc $rc; output $o"
}

# Joins two runs on file + name and prints each test whose status changed,
# with the B side message for a new failure.
diff_runs() {
  local a=$OUT/$1/results.jsonl b=$OUT/$2/results.jsonl
  [[ -f $a && -f $b ]] || { echo "missing results: $a or $b" >&2; exit 2; }
  node -e '
    const fs = require("fs");
    const load = f => {
      const m = new Map();
      for (const line of fs.readFileSync(f, "utf8").split("\n")) {
        if (!line) continue;
        const r = JSON.parse(line);
        let k = `${r.file} :: ${r.name}`;
        for (let i = 2; m.has(k); i++) k = `${r.file} :: ${r.name} #${i}`;
        m.set(k, r);
      }
      return m;
    };
    const [A, B] = [load(process.argv[1]), load(process.argv[2])];
    const keys = [...new Set([...A.keys(), ...B.keys()])].sort();
    const n = {};
    for (const k of keys) {
      const sa = A.get(k)?.status ?? "absent", sb = B.get(k)?.status ?? "absent";
      if (sa === sb) continue;
      const kind = (B.get(k) ?? A.get(k)).kind;
      n[`${sa}->${sb}`] = (n[`${sa}->${sb}`] ?? 0) + 1;
      console.log(`${sa} -> ${sb}  [${kind}] ${k}`);
      const msg = B.get(k)?.msg;
      if (sb === "fail" && msg) console.log("    " + msg.split("\n").slice(0, 12).join("\n    "));
    }
    console.log("changes", JSON.stringify(n));
  ' "$a" "$b"
}

case ${1:-} in
  run) [[ $# -eq 3 ]] || usage; run "$2" "$3" ;;
  diff) [[ $# -eq 3 ]] || usage; diff_runs "$2" "$3" ;;
  *) usage ;;
esac
