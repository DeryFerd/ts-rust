#!/usr/bin/env bash
# Builds the wasm module of the npm package npm/wasm: crates/ts_wasm for
# wasm32-wasip1 with the `wasm` size profile, then binaryen's wasm-opt.
#
# usage: scripts/wasm/build.sh [out.wasm]   (default npm/wasm/ts_rust.wasm)
# env:   WASM_PROFILE   cargo profile (default wasm; release for a fast build)
#        WASM_OPT       wasm-opt flags (default -Oz); "none" skips wasm-opt
# needs: rustup target add wasm32-wasip1; wasm-opt (binaryen 132 or later)
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
out="${1:-$repo/npm/wasm/ts_rust.wasm}"
profile="${WASM_PROFILE:-wasm}"
opt="${WASM_OPT:--Oz}"

cargo_cmd=(cargo)
# The capped runner needs systemd (Linux hosts such as zbook).
if command -v systemd-run >/dev/null; then
  cargo_cmd=("$repo/scripts/run-cargo-capped.sh")
fi
"${cargo_cmd[@]}" build --profile "$profile" -p ts_wasm --target wasm32-wasip1

target_dir="${CARGO_TARGET_DIR:-$repo/target}"
built="$target_dir/wasm32-wasip1/$profile/ts_wasm.wasm"
mkdir -p "$(dirname "$out")"
if [[ "$opt" == none ]]; then
  cp "$built" "$out"
else
  # The features that rustc enables for wasm32-wasip1 by default.
  # shellcheck disable=SC2086
  wasm-opt $opt --enable-bulk-memory --enable-nontrapping-float-to-int \
    --enable-sign-ext --enable-mutable-globals --enable-multivalue \
    --enable-reference-types --strip-debug --strip-producers \
    "$built" -o "$out"
fi

size() { wc -c <"$1" | tr -d ' '; }
echo "built:  $(size "$built") bytes ($built)"
echo "output: $(size "$out") bytes ($out)"
echo "gzip:   $(gzip -9 -c "$out" | wc -c | tr -d ' ') bytes"
if command -v brotli >/dev/null; then
  echo "brotli: $(brotli -q 11 -c "$out" | wc -c | tr -d ' ') bytes"
fi
