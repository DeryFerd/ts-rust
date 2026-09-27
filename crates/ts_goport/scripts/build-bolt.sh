#!/usr/bin/env bash
# Post-link BOLT of the timed bins, tsgo and goport (perf9 round 3, r3-link).
# The checker is limited by the instruction cache: its hot code is spread
# over many pages. BOLT puts the hot blocks of each function together and
# moves the cold blocks out. In relocation mode it also orders the
# functions. The program does not change, only where its code sits.
#
# Usage: build-bolt.sh <bin-dir> [out-dir]
#   bin-dir  holds tsgo and goport, for example the PGO bins
#            <pgo-out>/target-use/goport of scripts/build-pgo.sh
#   out-dir  default: <bin-dir>/../bolt. Must not have bin/ or work/ yet.
#            The BOLT bins land in <out-dir>/bin only when every identity
#            check passes. Else the script writes no bins and exits 1; keep
#            using <bin-dir>. The merged profiles, logs and identity
#            outputs stay in <out-dir>/work (summary: work/summary.txt).
#
# Run it on zbook. It needs perf LBR samples (perf record -j any,u works
# there at perf_event_paranoid 2). perf cannot profile on cup2 and alvin.
# Tools: perf, perf2bolt, merge-fdata, llvm-bolt, llvm-objcopy, llvm-nm,
# strace, readelf, taskset.
#
# Static bins (build-pgo.sh PGO_LINK=static, no INTERP) are refused. Tested
# with LLVM 23 BOLT on static glibc 2.44 test bins: relocation mode stops on
# the jump tables of glibc's assembly ("unclaimed PC-relative relocation"),
# and the non-relocation copy crashes at start, because crtbeginT's
# frame_dummy registers the old .eh_frame, which BOLT rewrote, with the
# libgcc unwinder. PIE and nopie (dynamic) bins work in both modes.
#
# Steps, for tsgo and goport:
#   1. Copy the bin to work/sym. Rename the symbols that have ".warm" or
#      ".cold" inside the name, for example the legacy-mangled
#      drop_in_place<Session::warm_auto_import_cache::{{closure}}>, which
#      has "..warm_auto". BOLT reads "<parent>.warm..." as a split fragment
#      of <parent> and stops with "parent function not found". The rename is
#      here and not in source, because project/session.rs differs on other
#      tracks. Real fragments (the name ends in .cold or .cold.N, from GCC
#      code in static glibc) keep their names. Only .symtab changes; the
#      code and the build id stay.
#   2. Read the GLIBC_TUNABLES (or _RJEM_MALLOC_CONF) value that the bin
#      sets for itself when it re-execs (strace -e execve), once for each
#      CPU set (arena_max can depend on the core count). The profile runs
#      set it, so the bin does not re-exec: perf2bolt maps the samples of
#      one exec only.
#   3. perf record -e cycles:u -j any,u of the five projects in the timed
#      form (tsgo: -p <cfg> --noEmit --pretty false --tsBuildInfoFile <tmp>;
#      goport: -p <cfg>), at 4 cores and at 16 threads. The sample periods
#      give each project about the same weight.
#   4. perf2bolt for each run, then merge-fdata.
#   5. llvm-bolt. Relocation mode when the bin has .rela.text (build-pgo.sh
#      links the use build with --emit-relocs): -reorder-blocks=ext-tsp
#      -reorder-functions=cdsort -split-functions -split-all-cold -split-eh.
#      Else non-relocation mode, where functions stay in place:
#      -reorder-blocks=ext-tsp -split-functions -split-all-cold. No
#      -hugify: it adds BOLT runtime code, which needs Theo's approval.
#   6. Identity: stdout, stderr and exit code of each BOLT bin equal those
#      of the input bin on the five projects at 4 cores and 16 threads. These
#      runs do not set the tunables, so they also check the re-exec.
#   7. Copy the BOLT bins to <out-dir>/bin, with bins.sha256.
#
# Environment:
#   GOPORT_DATA_ROOT  checkout that holds target/project-inputs (default: the
#                     main checkout of this repository)
#   BOLT_CPUS_4       CPUs of the 4-core runs (default 0,2,4,6: one thread
#                     per core on zbook)
#   BOLT_CPUS_16      CPUs of the 16-thread runs (default 0-15: 8 cores with
#                     SMT, like the 16 vCPU of cup2)
#   BOLT_PERF_CPUS    CPUs of perf itself (default 17,19,21,23)
#
# The runs only read project inputs: tsgo writes its .tsbuildinfo to a temp
# file, and every run starts in a temp directory.
set -euo pipefail

if (($# < 1 || $# > 2)); then
  echo "usage: build-bolt.sh <bin-dir> [out-dir]" >&2
  exit 2
fi
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd -- "$script_dir/../../.." && pwd)"
data_root="${GOPORT_DATA_ROOT:-$(cd -- "$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)/.." && pwd)}"
in_dir="$(cd -- "$1" && pwd)"
out="${2:-$in_dir/../bolt}"
declare -A cpus=([4]="${BOLT_CPUS_4:-0,2,4,6}" [16]="${BOLT_CPUS_16:-0-15}")
perf_cpus="${BOLT_PERF_CPUS:-17,19,21,23}"
bins=(tsgo goport)
cores=(4 16)

for tool in perf perf2bolt merge-fdata llvm-bolt llvm-objcopy llvm-nm strace readelf taskset; do
  command -v "$tool" > /dev/null || { echo "error: $tool not found" >&2; exit 1; }
done
for b in "${bins[@]}"; do
  [[ -x "$in_dir/$b" ]] || { echo "error: $in_dir/$b not found" >&2; exit 1; }
  if [[ "$(readelf -lW "$in_dir/$b")" != *" INTERP "* ]]; then
    echo "error: $in_dir/$b is static; BOLT breaks static glibc bins (see the header)" >&2
    exit 1
  fi
done
P="$data_root/target/project-inputs"
X="$data_root/target/project-inputs-extra"
declare -A projects=(
  [query]="$P/query/source/packages/query-core/tsconfig.prod.json"
  [hono]="$P/hono/source/tsconfig.build.json"
  [zod]="$P/zod/source/packages/zod/tsconfig.json"
  [effect]="$P/effect/source/packages/effect/tsconfig.json"
  [elysia]="$X/elysia/src/tsconfig.json"
)
names=(query hono zod effect elysia)
for p in "${names[@]}"; do
  [[ -f "${projects[$p]}" ]] || { echo "error: ${projects[$p]} not found" >&2; exit 1; }
done
# Sample periods (cycles): about 10k to 50k samples a run on zbook.
declare -A period=([query]=20011 [hono]=50021 [zod]=100003 [effect]=100003 [elysia]=1000003)

mkdir -p "$out"
out="$(cd -- "$out" && pwd)"
work="$out/work"
if [[ -e "$out/bin" || -e "$work" ]]; then
  echo "error: $out already has bin/ or work/; use a new out-dir" >&2
  exit 1
fi
mkdir -p "$work/sym" "$work/bolt" "$work/ident"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
# The bins re-exec with their own values only when these are unset
# (bin/goport.rs set_malloc_tunables), as in the timed runs.
unset GLIBC_TUNABLES _RJEM_MALLOC_CONF

say() { echo "$*" | tee -a "$work/summary.txt"; }
say "build-bolt $(date -Is) on $(hostname), input $in_dir"
(cd "$in_dir" && sha256sum "${bins[@]}") | tee "$work/input.sha256" | tee -a "$work/summary.txt"

# has_relocs <bin>: the bin was linked with --emit-relocs. (No grep -q in a
# pipe: with pipefail, readelf can die of SIGPIPE.)
has_relocs() { [[ "$(readelf -SW "$1")" == *" .rela.text"* ]]; }

# args_of <bin> <project> <tsbuildinfo>: sets `args` to the timed form.
args_of() {
  if [[ $1 == tsgo ]]; then
    args=(-p "${projects[$2]}" --noEmit --pretty false --tsBuildInfoFile "$3")
  else
    args=(-p "${projects[$2]}")
  fi
}

declare -A tunables mode
for b in "${bins[@]}"; do
  # 1. Rename the symbols that BOLT would read as fragments.
  sym="$work/sym/$b"
  llvm-nm -j --defined-only "$in_dir/$b" | sort -u |
    awk '/\.(cold|warm)/ && !/\.(cold|warm)(\.[0-9]+)?$/ {
      n = $0; gsub(/\.cold/, "_cold", n); gsub(/\.warm/, "_warm", n); print $0, n }' \
      > "$work/sym/$b.renames"
  if [[ -s "$work/sym/$b.renames" ]]; then
    llvm-objcopy --redefine-syms="$work/sym/$b.renames" "$in_dir/$b" "$sym"
    chmod +x "$sym"
  else
    cp -p "$in_dir/$b" "$sym"
  fi
  say "$b: renamed $(wc -l < "$work/sym/$b.renames") symbols"

  # 2. The re-exec value at each CPU set.
  for c in "${cores[@]}"; do
    trace="$work/strace-$b-c$c.txt"
    taskset -c "${cpus[$c]}" strace -f -qq -v -s 4096 -e trace=execve -e signal=none -o "$trace" \
      "$sym" --version > /dev/null 2>&1 || true
    tunables[$b-$c]="$({ grep -oE '"(GLIBC_TUNABLES|_RJEM_MALLOC_CONF)=[^"]*"' "$trace" || true; } | tail -1 | tr -d '"')"
    say "$b c$c: re-exec env ${tunables[$b-$c]:-none (no re-exec seen)}"
  done

  if has_relocs "$sym"; then mode[$b]=relocation; else mode[$b]=non-relocation; fi
done

# 3 and 4. Profiles. perf runs on its own CPUs.
for b in "${bins[@]}"; do
  for c in "${cores[@]}"; do
    for p in "${names[@]}"; do
      run="$b-c$c-$p"
      args_of "$b" "$p" "$tmp/$run.tsbuildinfo"
      # perf returns 0 even when the bin exits 1 (projects with diagnostics).
      (cd "$tmp" && env ${tunables[$b-$c]:+"${tunables[$b-$c]}"} taskset -c "$perf_cpus" \
        perf record -m 128 -e cycles:u -j any,u -c "${period[$p]}" -o "$work/$run.data" -- \
        taskset -c "${cpus[$c]}" "$work/sym/$b" "${args[@]}" > /dev/null 2> "$work/$run.err") || true
      rm -f "$tmp/$run.tsbuildinfo"
      [[ -s "$work/$run.data" ]] || { tail -5 "$work/$run.err" >&2; echo "error: perf record failed for $run" >&2; exit 1; }
      log="$work/$run.p2b.log"
      perf2bolt -p "$work/$run.data" -o "$work/$run.fdata" "$work/sym/$b" > "$log" 2>&1 ||
        { tail -5 "$log" >&2; echo "error: perf2bolt failed for $run" >&2; exit 1; }
      objects="$(sed -n 's/.*wrote \([0-9]*\) objects.*/\1/p' "$log")"
      if [[ -z "$objects" || "$objects" == 0 ]]; then
        echo "error: perf2bolt mapped no samples for $run (did the bin re-exec?)" >&2
        exit 1
      fi
      say "profile $run: $objects objects"
      rm -f "$work/$run.data"
    done
  done
  merge-fdata -o "$work/$b.fdata" "$work/$b"-c*.fdata > "$work/$b.merge.log" 2>&1
  rm -f "$work/$b"-c*.fdata
done

# 5. BOLT.
for b in "${bins[@]}"; do
  if [[ ${mode[$b]} == relocation ]]; then
    flags=(-reorder-blocks=ext-tsp -reorder-functions=cdsort -split-functions -split-all-cold -split-eh -dyno-stats)
  else
    flags=(-reorder-blocks=ext-tsp -split-functions -split-all-cold -dyno-stats)
  fi
  log="$work/$b.bolt.log"
  llvm-bolt "$work/sym/$b" -o "$work/bolt/$b" -data="$work/$b.fdata" "${flags[@]}" > "$log" 2>&1 ||
    { tail -5 "$log" >&2; echo "error: llvm-bolt failed for $b" >&2; exit 1; }
  if [[ ${mode[$b]} == relocation ]] && ! grep -q 'enabling relocation mode' "$log"; then
    echo "error: llvm-bolt did not use relocation mode for $b" >&2
    exit 1
  fi
  say "$b: ${mode[$b]} mode, flags ${flags[*]}"
  grep -E 'have non-empty execution profile|splitting separates|modified layout|functions were overwritten|Functions were reordered' "$log" |
    sed "s/^/$b: /" | tee -a "$work/summary.txt"
done

# 6. Identity of the BOLT bins with the input bins.
fail=0
for b in "${bins[@]}"; do
  for c in "${cores[@]}"; do
    for p in "${names[@]}"; do
      run="$b-c$c-$p"
      args_of "$b" "$p" "$tmp/$run-in.tsbuildinfo"
      rc_in=0
      (cd "$tmp" && taskset -c "${cpus[$c]}" "$in_dir/$b" "${args[@]}" \
        > "$work/ident/$run-in.out" 2> "$work/ident/$run-in.err") || rc_in=$?
      args_of "$b" "$p" "$tmp/$run-bolt.tsbuildinfo"
      rc_bolt=0
      (cd "$tmp" && taskset -c "${cpus[$c]}" "$work/bolt/$b" "${args[@]}" \
        > "$work/ident/$run-bolt.out" 2> "$work/ident/$run-bolt.err") || rc_bolt=$?
      rm -f "$tmp/$run"-*.tsbuildinfo
      same=EQUAL
      if [[ $rc_in != "$rc_bolt" ]] ||
        ! cmp -s "$work/ident/$run-in.out" "$work/ident/$run-bolt.out" ||
        ! cmp -s "$work/ident/$run-in.err" "$work/ident/$run-bolt.err"; then
        same=DIFF
        fail=1
      fi
      say "identity $run: rc $rc_in/$rc_bolt stdout $(sha256sum < "$work/ident/$run-in.out" | cut -c1-12) $same"
    done
  done
done
if ((fail)); then
  say "error: a BOLT bin differs from its input; no bins written. Keep $in_dir."
  exit 1
fi

# 7. Output.
mkdir "$out/bin"
mv "${bins[@]/#/$work/bolt/}" "$out/bin/"
(cd "$out/bin" && sha256sum "${bins[@]}" > bins.sha256)
rm -f "${bins[@]/#/$work/sym/}"
say "BOLT bins in $out/bin: ${bins[*]}"
