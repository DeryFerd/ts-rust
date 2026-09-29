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
#   5. Optional: scripts/build-bolt.sh <out-dir>/target-use/goport gives
#      BOLT copies of tsgo and goport (see its header).
#
# Link layout of the use build (perf9 round 3, r3-link). It adds two lld
# flags. The code does not change:
#   -z keep-text-section-prefix  keeps the .text.hot and .text.unlikely
#       groups that LLVM makes from the profile as their own sections, so hot
#       code sits together. Without it lld mixes them into .text. This is
#       the layout when BOLT is not used.
#   --emit-relocs  keeps the static relocations in the file (non-alloc
#       sections, not mapped at run time). BOLT needs them for relocation
#       mode, where it also reorders functions.
# The build prints the .text and .rela.text sections of tsgo
# (readelf -S). Expect .text.hot, .text.unlikely and .rela.text.
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
#   PGO_LINK          link mode of both builds (opt-in; default: PIE, as
#                     before):
#                     nopie   -C relocation-model=static: a non-PIE
#                             executable (ELF type EXEC), still dynamic.
#                     static  nopie and -C target-feature=+crt-static: a
#                             static non-PIE executable (EXEC, no INTERP),
#                             like Go tsgo.
#                     Why: one exec of the 32 MB dynamic PIE costs about
#                     3.3 ms on cup2 (350 to 430 page faults; 146 are ld.so
#                     copy-on-write faults for 28,002 relative relocations),
#                     and a run execs twice (the malloc tunables re-exec).
#                     These builds pass --target <host>, so build scripts
#                     and proc macros do not get the flags. The bins are
#                     copied to the usual <target>/goport path. The build
#                     checks the ELF type and INTERP of tsgo.
#
# Choosing PGO_LINK (integrator, once a round): build the default and
# PGO_LINK=static. On cup2 (under its lock) time 'tsgo --version' and query
# at 4 and 16 cores, with minor faults (/usr/bin/time -f %R or getrusage
# ru_minflt; perf is blocked on cup2). Keep static only
# when it is faster at both core counts; else try nopie the same way; else
# keep the default. Check that the GLIBC_TUNABLES re-exec still happens:
#   strace -f -qq -v -s 4096 -e trace=execve -e signal=none tsgo --version
# shows two execve calls, the second with GLIBC_TUNABLES=...
# build-bolt.sh refuses static bins (BOLT breaks static glibc; see its
# header). So when BOLT is used, compare static without BOLT against the
# BOLT copy of nopie or of the default.
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
# The training runs start no tsgo worker (bin/tsgo.rs `launch`): when the
# launcher exits, the parent death signal can kill the worker before it has
# written its profile.
export GOPORT_LAUNCH=0
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

link="${PGO_LINK:-}"
case "$link" in
  "") link_flags="" ;;
  nopie) link_flags="-Crelocation-model=static" ;;
  static) link_flags="-Crelocation-model=static -Ctarget-feature=+crt-static" ;;
  *) echo "error: PGO_LINK must be empty, nopie or static (got '$link')" >&2; exit 1 ;;
esac

# Each step needs its own target (other RUSTFLAGS). sccache is off: it could
# reuse an object built with an older profile at the same path.
build() { # build <target-subdir> <rustflags>
  local target="$out/$1" flags="$2" target_args=()
  # Both builds get the same link mode, so the profile of the generate build
  # matches the code of the use build. With --target, RUSTFLAGS apply only
  # to the target crates, not to build scripts and proc macros (a proc
  # macro cannot be +crt-static).
  if [[ -n "$link_flags" ]]; then
    flags+=" $link_flags"
    target_args=(--target "$host")
  fi
  echo "== build $1 ($flags)"
  # shellcheck disable=SC2086
  env CARGO_TARGET_DIR="$target" TS_CARGO_SEPARATE_TARGET=1 TS_CARGO_SCCACHE=0 RUSTFLAGS="$flags" \
    "${cargo_cmd[@]}" build --profile goport --offline --locked -p ts_goport --bins \
    "${target_args[@]}" $features \
    > "$out/build-$1.log" 2>&1 || { tail -20 "$out/build-$1.log" >&2; exit 1; }
  # With --target cargo writes the bins to <target>/<host>/goport. Copy them
  # to <target>/goport, where they are without --target.
  if [[ -n "$link_flags" ]]; then
    mkdir -p "$target/goport"
    find "$target/$host/goport" -maxdepth 1 -type f -executable -exec cp -p -t "$target/goport" {} +
  fi
}

# check_link <bin>: stops when the ELF type or INTERP does not match PGO_LINK.
check_link() {
  [[ -n "$link" ]] || return 0
  local type interp=no want
  type="$(readelf -h "$1" | sed -n 's/^ *Type: *\([A-Z]*\).*/\1/p')"
  [[ "$(readelf -lW "$1")" == *" INTERP "* ]] && interp=yes
  if [[ "$link" == static ]]; then want="EXEC no"; else want="EXEC yes"; fi
  echo "link $link: $1 type $type interp $interp"
  if [[ "$type $interp" != "$want" ]]; then
    echo "error: PGO_LINK=$link wants type/interp '$want', got '$type $interp'" >&2
    exit 1
  fi
}

# 1. Instrumented build.
build target-gen "-Cprofile-generate=$profiles"
gen="$out/target-gen/goport"
check_link "$gen/tsgo"

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
# The link args are the r3-link layout (see the header).
build target-use "-Cprofile-use=$merged -Clink-arg=-Wl,--emit-relocs -Clink-arg=-Wl,-z,keep-text-section-prefix"
if grep -q "profile format version\|profile-use" "$out/build-target-use.log"; then
  grep "profile format version\|profile-use" "$out/build-target-use.log" | head -3 >&2
  echo "error: rustc did not use the profile; the binaries are not PGO builds" >&2
  exit 1
fi
use="$out/target-use/goport"
check_link "$use/tsgo"
sections="$(readelf -SW "$use/tsgo" | grep -oE ' \.(rela\.)?text[.a-z]*' | sort -u | tr -d ' ' | tr '\n' ' ')"
echo "tsgo sections: $sections"
[[ " $sections " == *" .text.hot "* ]] || echo "warning: tsgo has no .text.hot section" >&2
[[ " $sections " == *" .rela.text "* ]] || echo "warning: tsgo has no .rela.text; BOLT runs in non-relocation mode" >&2
echo "PGO binaries: $out/target-use/goport/{goport,goport_emit,goport_build,goport_typesyms,tsgo}"
