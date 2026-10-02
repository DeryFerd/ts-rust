#!/usr/bin/env bash
# Builds the wasm module of the npm package npm/wasm: crates/ts_wasm for
# wasm32-wasip1 with the `wasm` size profile, then binaryen's wasm-opt.
#
# usage: scripts/wasm/build.sh [out.wasm]   (default npm/wasm/ts_rust.wasm)
# env:   WASM_PROFILE    cargo profile (default wasm; release for a fast build)
#        WASM_RUSTFLAGS  added to RUSTFLAGS (default none)
#        WASM_OPT        wasm-opt flags (default "-Oz --converge"); "none"
#                        skips wasm-opt
# needs: rustup target add wasm32-wasip1; wasm-opt (binaryen 132 or later)
#
# The default is the smallest module (opt-level z, 5.7 MB). For checks about
# 18% faster at 6.9 MB:
#   CARGO_PROFILE_WASM_OPT_LEVEL=s \
#   WASM_RUSTFLAGS="-C llvm-args=-inlinehint-threshold=150" scripts/wasm/build.sh
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
out="${1:-$repo/npm/wasm/ts_rust.wasm}"
profile="${WASM_PROFILE:-wasm}"
opt="${WASM_OPT:--Oz --converge}"

# At opt-level "s", LLVM inlines `#[inline]` functions up to cost 325; the
# faster build above lowers that to 150.
rustflags="${WASM_RUSTFLAGS:-}"
if [[ -n "$rustflags" ]]; then
  export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }$rustflags"
fi

cargo_cmd=(cargo)
# The capped runner needs a systemd user session (Linux hosts such as
# zbook). CI runners have systemd-run but no user session.
if [[ -z "${CI:-}" ]] && command -v systemd-run >/dev/null; then
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
