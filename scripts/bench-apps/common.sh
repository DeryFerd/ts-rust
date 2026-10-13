#!/usr/bin/env bash
# Shared paths and measurement checks for run.sh and t3code.sh.
# The callers use the tool paths and supply names and sel.
# shellcheck disable=SC2034,SC2154
bench_tools() {
  local work=$1
  case "$(uname -s)/$(uname -m)" in
    Linux/x86_64) platform=linux-x64; bun_platform=linux-x64 ;;
    Darwin/arm64) platform=darwin-arm64; bun_platform=darwin-aarch64 ;;
    *) echo "unsupported benchmark platform" >&2; exit 1 ;;
  esac
  RS_PKG=$work/node_modules/@tsc-rs/$platform/lib/tsc
  RS=${RS_BIN:-$RS_PKG}
  GO=$work/node_modules/@typescript/typescript-$platform/lib/tsc
  BUN=$work/bun-$bun_platform/bun
}

# Keep every preflight's full output. Reject crashes and require every timed
# run to have the same exit code as its preflight; diagnostic exits are valid.
bench_measure() {
  local out=$1; shift
  local cmds=("$@") args=() i rc
  [[ ! -e $out.json ]] || { echo "result already exists: $out.json" >&2; exit 1; }
  : >"$out.errors"
  for i in "${sel[@]}"; do
    rc=0
    bash -c "${cmds[$i]}" >"$out.${names[$i]}.stdout" 2>"$out.${names[$i]}.stderr" || rc=$?
    ((rc <= 2)) || { echo "${names[$i]} failed: exit $rc" >&2; exit 1; }
    cat "$out.${names[$i]}.stdout" "$out.${names[$i]}.stderr" |
      LC_ALL=C grep -E '(error|warning|message|suggestion) (TS-?[0-9]+|effect\()' |
      LC_ALL=C sort >"$out.${names[$i]}.diag" || true
    echo "${names[$i]} rc=$rc errors=$(wc -l <"$out.${names[$i]}.diag" | tr -d ' ')" >>"$out.errors"
    args+=(-n "${names[$i]}" "${cmds[$i]}")
  done
  echo "$(basename "$out"): $(tr '\n' ' ' <"$out.errors")"
  hyperfine -N -i --warmup 1 --runs "${RUNS:-5}" --export-json "$out.json" "${args[@]}"
  python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[1])
codes = {row.split()[0]: int(row.split()[1].split('=')[1])
         for row in Path(str(out) + '.errors').read_text().splitlines()}
for run in json.loads(Path(str(out) + '.json').read_text())['results']:
    if not all(code == codes[run['command']] for code in run['exit_codes']):
        raise SystemExit(f"inconsistent exits: {run['command']}: {run['exit_codes']}")
PY
}
