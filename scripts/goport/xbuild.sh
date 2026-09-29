#!/usr/bin/env bash
# Cross-builds (compiles and links) the release tsgo binary for the targets that Go's npm packages
# ship, with cargo-zigbuild (zig as the C compiler and linker) through scripts/run-cargo-capped.sh.
#
# usage: scripts/goport/xbuild.sh [--out <dir>] [--bin <name>] [--no-default-features] [<target>...]
#
#   <target>   Rust target triples. Default: aarch64-unknown-linux-gnu x86_64-unknown-linux-musl
#              aarch64-unknown-linux-musl aarch64-apple-darwin x86_64-apple-darwin x86_64-pc-windows-gnu
#   --out      Result dir (default <checkout>/target/goport-xbuild/<short HEAD>). It holds, per target,
#              <target>/<bin>[.exe], <target>/build.log, and the files COMMIT, SUMMARY.tsv and bins.sha256.
#   --bin      The bin to build (default tsgo). Repeat it for more bins.
#   --no-default-features
#              Build without jemalloc (glibc or system malloc).
#
# Each target is one cargo call, so other lanes can take the shared cargo lock between targets. The
# build uses the default toolchain (--release is not an edit-loop build), --locked, and the checkout's
# own target dir (<checkout>/target/<target>/release). Needs cargo-zigbuild, zig and `rustup target add`
# for each target. zig ships the libc stubs for Linux (glibc and musl), macOS (libSystem) and MinGW, so no
# macOS SDK or MinGW toolchain is needed as long as nothing links a macOS framework.
# SUMMARY.tsv: target, LINK or FAIL rc=<N>, seconds, `file` output. Last stdout line: DONE, or FAIL rc=1
# when a target did not link.
set -uo pipefail

{
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
CO=$(cd -- "$here/../.." && pwd)
DEFAULT_TARGETS=(aarch64-unknown-linux-gnu x86_64-unknown-linux-musl aarch64-unknown-linux-musl
  aarch64-apple-darwin x86_64-apple-darwin x86_64-pc-windows-gnu)

out=""
bins=()
features=()
targets=()
while (($#)); do
  case "$1" in
    --out) out=$2; shift 2 ;;
    --bin) bins+=("$2"); shift 2 ;;
    --no-default-features) features+=(--no-default-features); shift ;;
    -h | --help) sed -n '2,/^set -uo/p' "$0" | sed '$d'; exit 0 ;;
    -*) echo "xbuild.sh: unknown option $1" >&2; echo "FAIL rc=2"; exit 2 ;;
    *) targets+=("$1"); shift ;;
  esac
done
((${#targets[@]})) || targets=("${DEFAULT_TARGETS[@]}")
((${#bins[@]})) || bins=(tsgo)
commit=$(git -C "$CO" rev-parse HEAD)
out=$(realpath -m -- "${out:-$CO/target/goport-xbuild/${commit:0:9}}")
mkdir -p "$out"
echo "$commit" >"$out/COMMIT"
git -C "$CO" status --porcelain -- crates Cargo.toml Cargo.lock >"$out/DIRTY"
[[ -s $out/DIRTY ]] || rm -f "$out/DIRTY"
: >"$out/SUMMARY.tsv"

command -v cargo-zigbuild >/dev/null || { echo "xbuild.sh: cargo-zigbuild is not installed" >&2; echo "FAIL rc=2"; exit 2; }
installed=$(rustup target list --installed)

bin_args=()
for b in "${bins[@]}"; do bin_args+=(--bin "$b"); done

failed=0
for t in "${targets[@]}"; do
  dir=$out/$t
  mkdir -p "$dir"
  log=$dir/build.log
  if ! grep -qx -- "$t" <<<"$installed"; then
    printf '%s\tFAIL rc=2\t0\trustup target %s is not installed\n' "$t" "$t" >>"$out/SUMMARY.tsv"
    echo "$t: not installed (rustup target add $t)"
    failed=1
    continue
  fi
  start=$(date +%s)
  (cd "$CO" && scripts/run-cargo-capped.sh zigbuild --release --locked -p ts_goport "${bin_args[@]}" \
    "${features[@]}" --target "$t") >"$log" 2>&1
  rc=$?
  secs=$(($(date +%s) - start))
  if ((rc == 0)); then
    desc=""
    for b in "${bins[@]}"; do
      exe=$b
      [[ $t == *windows* ]] && exe=$b.exe
      cp -f -- "$CO/target/$t/release/$exe" "$dir/$exe"
      desc+="$exe: $(file -b "$dir/$exe" | cut -c1-120); "
    done
    printf '%s\tLINK\t%s\t%s\n' "$t" "$secs" "$desc" >>"$out/SUMMARY.tsv"
    echo "$t: LINK (${secs}s)"
  else
    err=$(grep -m1 -E '^(error|  = note: .*(error|undefined))' "$log" | cut -c1-200)
    printf '%s\tFAIL rc=%s\t%s\t%s\n' "$t" "$rc" "$secs" "$err" >>"$out/SUMMARY.tsv"
    echo "$t: FAIL rc=$rc (${secs}s) $err"
    failed=1
  fi
done

(cd "$out" && find . -type f ! -name '*.log' ! -name bins.sha256 ! -name SUMMARY.tsv ! -name COMMIT ! -name DIRTY \
  -print0 | sort -z | xargs -0r sha256sum) >"$out/bins.sha256"
column -t -s $'\t' "$out/SUMMARY.tsv" | cut -c1-200
if ((failed)); then echo "FAIL rc=1"; exit 1; fi
echo "DONE"
}
