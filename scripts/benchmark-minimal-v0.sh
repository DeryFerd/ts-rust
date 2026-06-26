#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"
rust_binary="${RUST_TS_GO:-${repo_root}/target/release/tsgo}"
oracle="${TS_GO_ORACLE:-/home/theo/.local/bin/tsgo-oracle}"
runs="${RUNS:-31}"

if [[ ! -x "$rust_binary" ]]; then
  echo "Rust compiler not found at $rust_binary; build it with scripts/run-cargo-capped.sh build --release -p ts_cli --bin tsgo" >&2
  exit 2
fi
if [[ ! -x "$oracle" ]]; then
  echo "Set TS_GO_ORACLE to the pinned executable Go oracle" >&2
  exit 2
fi
if [[ ! "$runs" =~ ^[1-9][0-9]*$ ]]; then
  echo "RUNS must be a positive integer" >&2
  exit 2
fi

temporary="$(mktemp -d "${TMPDIR:-/tmp}/ts-rust-minimal-v0.XXXXXX")"
trap 'rm -rf -- "$temporary"' EXIT

cd "$repo_root"
inputs=(
  benchmarks/minimal-v0/src/dep.ts
  benchmarks/minimal-v0/src/main.ts
  benchmarks/minimal-v0/src/view.tsx
  benchmarks/minimal-v0/src/legacy.js
  benchmarks/minimal-v0/src/widget.jsx
)
options=(
  --ignoreConfig
  --noCheck
  --target esnext
  --module esnext
  --jsx preserve
  --allowJs
  --pretty false
)
rust_output="$temporary/rust"
go_output="$temporary/go"

"$rust_binary" "${inputs[@]}" "${options[@]}" --outDir "$rust_output"
"$oracle" "${inputs[@]}" "${options[@]}" --outDir "$go_output"
diff -ru "$go_output" "$rust_output"

benchmark() {
  local binary="$1"
  local output="$2"
  local run start end

  "$binary" "${inputs[@]}" "${options[@]}" --outDir "$output" >/dev/null
  for run in $(seq 1 "$runs"); do
    start="$(date +%s%N)"
    "$binary" "${inputs[@]}" "${options[@]}" --outDir "$output" >/dev/null
    end="$(date +%s%N)"
    echo "$((end - start))"
  done | sort -n | awk -v count="$runs" '
    { values[NR] = $1 }
    END {
      median = values[int((count + 1) / 2)] / 1000000
      p95 = values[int((count * 95 + 99) / 100)] / 1000000
      printf "%.3f %.3f", median, p95
    }
  '
}

read -r rust_median rust_p95 <<<"$(benchmark "$rust_binary" "$rust_output")"
read -r go_median go_p95 <<<"$(benchmark "$oracle" "$go_output")"

printf 'rust median_ms=%s p95_ms=%s runs=%s\n' "$rust_median" "$rust_p95" "$runs"
printf 'go   median_ms=%s p95_ms=%s runs=%s\n' "$go_median" "$go_p95" "$runs"
awk -v rust="$rust_median" -v go="$go_median" 'BEGIN { printf "median_speedup=%.2fx\n", go / rust }'

measure_peak() {
  local binary="$1"
  local output="$2"

  if ! command -v python3 >/dev/null; then
    echo unavailable
    return
  fi
  python3 - "$repo_root" "$binary" "${inputs[@]}" "${options[@]}" --outDir "$output" <<'PY'
import resource
import subprocess
import sys

subprocess.run(
    sys.argv[2:],
    cwd=sys.argv[1],
    stdout=subprocess.DEVNULL,
    check=True,
)
print(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024)
PY
}

printf 'rust peak_rss_bytes=%s\n' "$(measure_peak "$rust_binary" "$rust_output")"
printf 'go   peak_rss_bytes=%s\n' "$(measure_peak "$oracle" "$go_output")"
