#!/usr/bin/env bash
# Builds the wasm module of the npm package npm/wasm: crates/ts_wasm for
# wasm32-wasip1 with the `wasm` size profile, then binaryen's wasm-opt, then
# a new function order for better compression (order-functions.mjs).
#
# usage: scripts/wasm/build.sh [out.wasm]   (default npm/wasm/ts_rust.wasm)
# env:   WASM_PROFILE    cargo profile (default wasm; release for a fast build)
#        WASM_RUSTFLAGS  added to RUSTFLAGS (default none)
#        WASM_OPT        wasm-opt flags (default "--flatten --rereloop -Oz -Oz");
#                        "none" skips wasm-opt and the function order
# needs: rustup target add wasm32-wasip1; wasm-opt (binaryen 132 or later);
#        node
#
# The default is the smallest module (opt-level z, 4.2 MB with Rust 1.98.1;
# 1.93.0 makes it 2% bigger). For checks 13 to 18% faster at 5.2 MB:
#   CARGO_PROFILE_WASM_OPT_LEVEL=s \
#   WASM_RUSTFLAGS="-C llvm-args=-inlinehint-threshold=150" scripts/wasm/build.sh
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
out="${1:-$repo/npm/wasm/ts_rust.wasm}"
profile="${WASM_PROFILE:-wasm}"
# --flatten --rereloop builds the control flow of each function again from
# its basic blocks, and the two -Oz runs then shrink it: 0.8% smaller raw,
# gzip and brotli than "-Oz --converge", at the same speed.
opt="${WASM_OPT:---flatten --rereloop -Oz -Oz}"

# At opt-level "s", LLVM inlines `#[inline]` functions up to cost 325; the
# faster build above lowers that to 150.
rustflags="${WASM_RUSTFLAGS:-}"
# The module keeps the source path of each panic location. Map the paths
# that name the build host, as cargo's trim-paths does: the repo to
# relative paths, a registry crate to `<name>-<version>/...`, and the
# toolchain's library source to `/rustc/<commit>`. RUSTFLAGS splits at
# spaces, so a path with a space keeps its name.
sysroot="$(rustc --print sysroot)"
commit="$(rustc -vV | sed -n 's/^commit-hash: //p')"
remaps=("$repo/=" "$sysroot/lib/rustlib/src/rust=/rustc/$commit")
for registry in "${CARGO_HOME:-$HOME/.cargo}"/registry/src/*/; do
  [[ -d "$registry" ]] && remaps+=("$registry=")
done
for remap in "${remaps[@]}"; do
  [[ "$remap" == *[[:space:]]* ]] || rustflags="${rustflags:+$rustflags }--remap-path-prefix=$remap"
done
export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }$rustflags"

cargo_cmd=(cargo)
# The capped runner needs a systemd user session (Linux hosts such as
# zbook). CI runners have systemd-run but no user session.
if [[ -z "${CI:-}" ]] && command -v systemd-run >/dev/null; then
  cargo_cmd=("$repo/scripts/run-cargo-capped.sh")
fi
target_dir="${CARGO_TARGET_DIR:-$repo/target}"
built="$target_dir/wasm32-wasip1/$profile/ts_wasm.wasm"
mkdir -p "$(dirname "$out")"
# Both paths use `cargo rustc`, so the capped runner builds with the default
# toolchain, as CI and macOS do (it picks nightly only for `cargo build`).
cargo_rustc=("${cargo_cmd[@]}" rustc --profile "$profile" -p ts_wasm --lib --target wasm32-wasip1)
if [[ "$opt" == none ]]; then
  "${cargo_rustc[@]}"
  cp "$built" "$out"
else
  # order-functions.mjs needs the function names, so the link keeps them
  # (-C strip=debuginfo). Only the final crate gets the flag: a profile
  # change would change every crate's hash, so every symbol name and some
  # of the code.
  "${cargo_rustc[@]}" -- -C strip=debuginfo
  # The features that rustc enables for wasm32-wasip1 by default.
  features=(--enable-bulk-memory --enable-nontrapping-float-to-int --enable-sign-ext
    --enable-mutable-globals --enable-multivalue --enable-reference-types)
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  # The order of the functions changes the compressed size a lot: at
  # 107d120d the order below saves 40 KB raw, 96 KB gzip and 22 KB brotli
  # (see order-functions.mjs). wasm-opt --reorder-functions made it worse.
  # 1. hide: names that keep wasm-opt's code the same as with no names.
  # 2. wasm-opt -g: optimize, and keep those names.
  # 3. key: name each function with its position in the new order.
  # 4. Reorder, and strip the names. -s 2 runs no pass, but lets the writer
  #    optimize the stack IR as the -Oz run did (else about 8 KB larger).
  node "$repo/scripts/wasm/order-functions.mjs" hide "$built" "$tmp/hidden.wasm"
  # shellcheck disable=SC2086
  wasm-opt $opt "${features[@]}" -g "$tmp/hidden.wasm" -o "$tmp/opt.wasm"
  node "$repo/scripts/wasm/order-functions.mjs" key "$tmp/opt.wasm" "$built" "$tmp/keyed.wasm"
  wasm-opt -s 2 --reorder-functions-by-name "${features[@]}" --strip-debug --strip-producers \
    "$tmp/keyed.wasm" -o "$out"
fi

size() { wc -c <"$1" | tr -d ' '; }
echo "built:  $(size "$built") bytes ($built)"
echo "output: $(size "$out") bytes ($out)"
echo "gzip:   $(gzip -9 -c "$out" | wc -c | tr -d ' ') bytes"
if command -v brotli >/dev/null; then
  echo "brotli: $(brotli -q 11 -c "$out" | wc -c | tr -d ' ') bytes"
fi
