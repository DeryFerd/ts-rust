#!/usr/bin/env bash
# Builds a PGO (profile-guided) release of the goport binaries on stable Rust,
# with the workspace `goport` cargo profile (fat LTO, one codegen unit).
#
# Usage: build-pgo.sh [out-dir]
#   out-dir  default: <data-root>/target/goport-pgo
#
# Steps:
#   1. goport-profile build with -Cprofile-generate (instrumented).
#   2. Training runs: goport and tsgo on query, hono, zod, effect and
#      elysia in the timed form (see below), goport on a spread of corpus
#      cases, and goport_emit on query and hono.
#   3. Merge the .profraw files with llvm-profdata.
#   4. goport-profile build with -Cprofile-use. The binaries (goport,
#      goport_emit, goport_build, goport_typesyms, tsgo) land in
#      <out-dir>/target-use/goport.
#
# Environment:
#   RUSTUP_TOOLCHAIN  default 1.95.0. Its LLVM 22 matches the system
#                     llvm-profdata (LLVM 22). 1.93 has LLVM 21 and cannot read
#                     the profile that LLVM 22 writes.
#   GOPORT_DATA_ROOT  checkout that holds target/project-inputs and the corpus
#                     (default: the main checkout of this repository)
#   LLVM_PROFDATA     llvm-profdata to use. Default: the rustup llvm-tools copy
#                     if present, else llvm-profdata on PATH. Its LLVM must not
#                     be newer than rustc's LLVM.
#   PGO_ALLOW_LLVM_MISMATCH=1  run anyway (step 4 then fails its check)
#   PGO_CORPUS_STEP   train on every Nth corpus case (default 60, about 200)
#   CARGO_FEATURES    extra cargo flags, for example "--features jemalloc".
#                     Retrain when the allocator or hot code changes.
#
# The training runs only read project inputs: goport does not write,
# goport_emit writes to a temp --outDir and tsgo writes its .tsbuildinfo to
# a temp file.
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd -- "$script_dir/../../.." && pwd)"
data_root="${GOPORT_DATA_ROOT:-$(cd -- "$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)/.." && pwd)}"
out="${1:-$data_root/target/goport-pgo}"
features="${CARGO_FEATURES:-}"
corpus_step="${PGO_CORPUS_STEP:-60}"
export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.95.0}"
mkdir -p "$out"
out="$(cd -- "$out" && pwd)"
# Run rustc and cargo from the repository. RUSTUP_TOOLCHAIN overrides any
# toolchain file there.
cd "$repo"

# llvm-profdata must read the raw profiles of rustc's LLVM and write an
# indexed profile that rustc's LLVM can read. A newer major version reads old
# raw profiles, but its indexed output can be too new; step 4 fails then.
sysroot="$(rustc --print sysroot)"
host="$(rustc -vV | sed -n 's/^host: //p')"
rustc_llvm="$(rustc -vV | sed -n 's/^LLVM version: \([0-9]*\).*/\1/p')"
profdata="${LLVM_PROFDATA:-}"
if [[ -z "$profdata" ]]; then
  if [[ -x "$sysroot/lib/rustlib/$host/bin/llvm-profdata" ]]; then
    profdata="$sysroot/lib/rustlib/$host/bin/llvm-profdata"
  else
    profdata="$(command -v llvm-profdata)"
  fi
fi
profdata_llvm="$("$profdata" --version | sed -n 's/.*LLVM version \([0-9]*\).*/\1/p' | head -1)"
echo "rustc $(rustc -V | cut -d' ' -f2) LLVM $rustc_llvm, $profdata LLVM $profdata_llvm"
# Example: rustc 1.93 (LLVM 21) cannot read the indexed format 13 that LLVM 22
# writes. It only warns and builds without the profile.
if ((profdata_llvm > rustc_llvm)) && [[ "${PGO_ALLOW_LLVM_MISMATCH:-0}" != 1 ]]; then
  echo "error: llvm-profdata (LLVM $profdata_llvm) is newer than rustc's LLVM $rustc_llvm." >&2
  echo "Run 'rustup component add llvm-tools' for this toolchain, or set LLVM_PROFDATA." >&2
  exit 1
fi

# Use the repository's memory-capped cargo wrapper when it exists.
cargo_cmd=(cargo)
[[ -x "$repo/scripts/run-cargo-capped.sh" ]] && cargo_cmd=("$repo/scripts/run-cargo-capped.sh")

profiles="$out/profiles"
merged="$out/goport.profdata"
rm -rf "$profiles"
mkdir -p "$profiles"

# Each step needs its own target (other RUSTFLAGS). sccache is off: it could
# reuse an object built with an older profile at the same path.
build() { # build <target-subdir> <rustflags>
  local target="$out/$1"
  echo "== build $1 ($2)"
  # shellcheck disable=SC2086
  env CARGO_TARGET_DIR="$target" TS_CARGO_SEPARATE_TARGET=1 TS_CARGO_SCCACHE=0 RUSTFLAGS="$2" \
    "${cargo_cmd[@]}" build --profile goport --offline --locked -p ts_goport --bins $features \
    > "$out/build-$1.log" 2>&1 || { tail -20 "$out/build-$1.log" >&2; exit 1; }
}

# 1. Instrumented build.
build target-gen "-Cprofile-generate=$profiles"
gen="$out/target-gen/goport"

# 2. Training. Exit codes are ignored: some inputs have diagnostics on purpose.
# The binaries re-exec with their built-in malloc string only when these are
# unset (bin/goport.rs set_malloc_tunables). The timed runs have them unset,
# so train the same way.
unset GLIBC_TUNABLES _RJEM_MALLOC_CONF
P="$data_root/target/project-inputs"
X="$data_root/target/project-inputs-extra"
declare -A projects=(
  [query]="$P/query/source/packages/query-core/tsconfig.prod.json"
  [hono]="$P/hono/source/tsconfig.build.json"
  [zod]="$P/zod/source/packages/zod/tsconfig.json"
  [effect]="$P/effect/source/packages/effect/tsconfig.json"
  [elysia]="$X/elysia/src/tsconfig.json"
)
for name in query hono zod effect elysia; do
  s=$SECONDS
  "$gen/goport" -p "${projects[$name]}" > /dev/null 2>&1 || true
  echo "train goport $name $((SECONDS - s))s"
done
emit_tmp="$(mktemp -d)"
trap 'rm -rf "$emit_tmp"' EXIT
# tsgo in the timed form: -p <cfg> --noEmit --pretty false --tsBuildInfoFile
# <temp>. --pretty false keeps FORCE_COLOR in the caller's env from training
# the pretty diagnostic path. Only incremental projects (hono, effect) use the
# build info file.
for name in query hono zod effect elysia; do
  s=$SECONDS
  "$gen/tsgo" -p "${projects[$name]}" --noEmit --pretty false \
    --tsBuildInfoFile "$emit_tmp/$name.tsbuildinfo" > /dev/null 2>&1 || true
  echo "train tsgo $name $((SECONDS - s))s"
done
for cfg in "${projects[query]}" "${projects[hono]}"; do
  "$gen/goport_emit" -p "$cfg" --outDir "$emit_tmp/out" > /dev/null 2>&1 || true
  rm -rf "$emit_tmp/out"
done
cases="$data_root/target/continuation-r97-goport/corpus-full/cases"
n=0
if [[ -d "$cases" ]]; then
  i=0
  for dir in "$cases"/*/; do
    if ((i++ % corpus_step == 0)) && [[ -f "$dir/tsconfig.json" ]]; then
      (cd "$dir" && timeout 60 "$gen/goport" -p tsconfig.json > /dev/null 2>&1) || true
      n=$((n + 1))
    fi
  done
fi
echo "train corpus $n cases, $(find "$profiles" -name '*.profraw' | wc -l) profraw files"

# 3. Merge.
"$profdata" merge -o "$merged" "$profiles"
echo "merged $(du -h "$merged" | cut -f1) -> $merged"

# 4. Optimized build. rustc only warns when it cannot read the profile, so
# check the log.
build target-use "-Cprofile-use=$merged"
if grep -q "profile format version\|profile-use" "$out/build-target-use.log"; then
  grep "profile format version\|profile-use" "$out/build-target-use.log" | head -3 >&2
  echo "error: rustc did not use the profile; the binaries are not PGO builds" >&2
  exit 1
fi
echo "PGO binaries: $out/target-use/goport/{goport,goport_emit,goport_build,goport_typesyms,tsgo}"
