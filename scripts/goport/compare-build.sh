#!/usr/bin/env bash
# U10: compare `goport_build -b` with `tsgo-oracle -b` on copies of real
# monorepos (build-mode plan, section 5).
#
# usage:
#   compare-build.sh init <repo> [keep-buildinfo]   make fresh oracle/goport copies
#   compare-build.sh step <repo> <label> [args...]  run `-b <entry> --verbose --pretty false args`
#                                                   with both tools and compare
#   compare-build.sh edit <repo> <touch|body|api|err|fix>
#                                                   apply the same edit to both copies
#   compare-build.sh seq <repo> [phase...]          run a scenario sequence
#                                                   (phases: cold edits flags foreign)
#
# repos: repro (ts-eslint repro/lib + repro/app), query (root tsconfig.json),
#        query-chain (query-sync-storage-persister chain), tseslint
#        (packages/utils/tsconfig.build.json), hono (root tsconfig.json).
#
# Copies live in /tmp/goport-build/<repo>/seq/{oracle,goport}. Both have the
# same depth, so relative paths in .tsbuildinfo agree. Inputs are never
# written: each copy is `cp -a` of the input without the top-level
# node_modules, which is a symlink to the input's node_modules.
#
# Per step it compares: exit code, stdout (copy root -> <ROOT>, status times
# masked), the set of output files written or touched (mtime changes), and
# the full output tree (diff -r). Results: /tmp/goport-build/<repo>/seq/log.
set -uo pipefail

REPO_ROOT=/home/theo/Code/sandbox/ts-rust
ORACLE=${ORACLE:-$HOME/.local/bin/tsgo-oracle}
GOPORT=${GOPORT_BUILD:-$REPO_ROOT/target/continuation-r97-goport/runtime/cargo-bm-integ/release/goport_build}
TIMEOUT=${TIMEOUT:-900}
INPUTS=$REPO_ROOT/target/project-inputs
EXTRA=$REPO_ROOT/target/project-inputs-extra/typescript-eslint-typescript-eslint-packages-utils

# repo -> source dir, entry config, upstream file for edits, api file
repo_config() {
  case $1 in
    repro) SRC=$EXTRA/repro; ENTRY=app/tsconfig.json
      UP_FILE=lib/src/a.ts; API_FILE=lib/src/index.ts ;;
    query) SRC=$INPUTS/query/source; ENTRY=tsconfig.json
      UP_FILE=eslint.config.js; API_FILE= ;;
    query-chain) SRC=$INPUTS/query/source; ENTRY=packages/query-sync-storage-persister/tsconfig.json
      UP_FILE=packages/query-core/src/utils.ts; API_FILE=packages/query-core/src/index.ts ;;
    tseslint) SRC=$EXTRA/src; ENTRY=packages/utils/tsconfig.build.json
      UP_FILE=packages/types/src/index.ts; API_FILE=packages/types/src/index.ts ;;
    hono) SRC=$INPUTS/hono/source; ENTRY=tsconfig.json
      UP_FILE=src/hono.ts; API_FILE=src/index.ts ;;
    *) echo "unknown repo $1" >&2; exit 2 ;;
  esac
  BASE=/tmp/goport-build/$1/seq
  LOG=$BASE/log
}

# cp -a without the top-level node_modules (symlinked instead), then make
# the copy writable (chmod -R does not follow symlinks while recursing).
make_copy() { # src dst
  mkdir -p "$2"
  local entry
  for entry in "$1"/* "$1"/.[!.]*; do
    [[ -e $entry || -L $entry ]] || continue
    if [[ $(basename "$entry") == node_modules && -d $entry && ! -L $entry ]]; then
      ln -s "$entry" "$2/node_modules"
    else
      cp -a "$entry" "$2/"
    fi
  done
  chmod -R u+w "$2"
}

cmd_init() {
  repo_config "$1"
  local keep=${2:-}
  rm -rf "$BASE"
  mkdir -p "$LOG"
  make_copy "$SRC" "$BASE/oracle"
  if [[ $keep != keep-buildinfo ]]; then
    find "$BASE/oracle" -path '*/node_modules' -prune -o -name '*.tsbuildinfo' -print0 | xargs -0 -r rm -f
  fi
  # The goport copy is a copy of the prepared oracle copy (same mtimes).
  mkdir -p "$BASE/goport"
  cp -a "$BASE/oracle/." "$BASE/goport/"
  echo "init $1 -> $BASE"
}

# Lists `path mtime sha1` of every non-input output file (not node_modules).
snapshot() { # copy_dir out
  (cd "$1" && find . -path '*/node_modules' -prune -o -type f \
    \( -name '*.js' -o -name '*.mjs' -o -name '*.cjs' -o -name '*.d.ts' -o -name '*.d.mts' \
       -o -name '*.d.cts' -o -name '*.map' -o -name '*.tsbuildinfo' \) -printf '%p %T@\n' \
    | sort | while read -r p t; do echo "$p $t $(sha1sum < "$p" | cut -c1-12)"; done) > "$2"
}

# Classifies changes between two snapshots: W (written: new or content changed),
# T (touched: same content, new mtime), D (deleted).
changes() { # before after
  python3 - "$1" "$2" <<'EOF'
import sys
def load(p):
    d = {}
    for line in open(p):
        path, t, h = line.split()
        d[path] = (t, h)
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
for p in sorted(set(a) | set(b)):
    if p not in b: print("D", p)
    elif p not in a: print("W", p)
    elif a[p][1] != b[p][1]: print("W", p)
    elif a[p][0] != b[p][0]: print("T", p)
EOF
}

normalize() { # root file
  sed -e "s#$1#<ROOT>#g" -e 's#^[0-9]\{1,2\}:[0-9]\{2\}:[0-9]\{2\} [AP]M - #<TIME> - #' "$2"
}

run_tool() { # tool_name copy_dir label args...
  local name=$1 dir=$2 label=$3; shift 3
  local bin=$ORACLE
  [[ $name == goport ]] && bin=$GOPORT
  snapshot "$dir" "$LOG/$label.$name.before"
  local start=$(date +%s.%N)
  # --clean cannot be combined with --verbose (TS6370).
  local verbose=--verbose
  [[ " $* " == *" --clean "* ]] && verbose=
  (cd "$dir" && timeout "$TIMEOUT" "$bin" -b "$ENTRY" $verbose --pretty false "$@" \
    > "$LOG/$label.$name.raw" 2> "$LOG/$label.$name.err")
  echo $? > "$LOG/$label.$name.exit"
  python3 -c 'import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),1))' "$start" "$(date +%s.%N)" \
    > "$LOG/$label.$name.time"
  snapshot "$dir" "$LOG/$label.$name.after"
  normalize "$dir" "$LOG/$label.$name.raw" > "$LOG/$label.$name.out"
  changes "$LOG/$label.$name.before" "$LOG/$label.$name.after" > "$LOG/$label.$name.changes"
}

# After a compared step, give each goport file the oracle's mtime when both copies have the same
# content. A step's output times depend on how fast each tool wrote. Without this, a clock tick
# between two writes in one copy but not the other changes which output a later "up to date"
# message names. Each step then starts from the same state, and is still compared exactly.
sync_mtimes() {
  python3 - "$BASE/oracle" "$BASE/goport" <<'EOF'
import filecmp, os, sys
oracle, goport = sys.argv[1:3]
for root, dirs, files in os.walk(oracle):
    dirs[:] = [d for d in dirs if d != "node_modules"]
    for name in files:
        o = os.path.join(root, name)
        g = os.path.join(goport, os.path.relpath(o, oracle))
        if os.path.islink(o) or not os.path.isfile(g) or os.path.islink(g):
            continue
        so = os.stat(o)
        if so.st_mtime_ns != os.stat(g).st_mtime_ns and filecmp.cmp(o, g, shallow=False):
            os.utime(g, ns=(so.st_atime_ns, so.st_mtime_ns))
EOF
}

cmd_step() {
  local repo=$1 label=$2; shift 2
  repo_config "$repo"
  run_tool oracle "$BASE/oracle" "$label" "$@"
  run_tool goport "$BASE/goport" "$label" "$@"
  local fail=()
  cmp -s "$LOG/$label.oracle.exit" "$LOG/$label.goport.exit" || fail+=("exit $(cat "$LOG/$label.oracle.exit")/$(cat "$LOG/$label.goport.exit")")
  diff "$LOG/$label.oracle.out" "$LOG/$label.goport.out" > "$LOG/$label.stdout.diff" || fail+=("stdout")
  diff "$LOG/$label.oracle.changes" "$LOG/$label.goport.changes" > "$LOG/$label.changes.diff" || fail+=("changes")
  diff -r -q --no-dereference -x node_modules "$BASE/oracle" "$BASE/goport" > "$LOG/$label.tree.diff" || fail+=("tree")
  # Readable diff of each differing .tsbuildinfo.
  grep -o '^Files .*\.tsbuildinfo and' "$LOG/$label.tree.diff" | sed 's/^Files //; s/ and$//' | while read -r f; do
    g=${f/#$BASE\/oracle/$BASE\/goport}
    diff <(python3 -m json.tool "$f") <(python3 -m json.tool "$g") > "$LOG/$label.$(basename "$f").json.diff"
  done
  local unported=$(grep -c '^unported' "$LOG/$label.goport.err")
  sync_mtimes
  if [[ ${#fail[@]} -eq 0 ]]; then
    echo "$repo $label MATCH (exit $(cat "$LOG/$label.oracle.exit"), $(grep -c '^W' "$LOG/$label.oracle.changes") written, $(grep -c '^T' "$LOG/$label.oracle.changes") touched, $(grep -c "^D" "$LOG/$label.oracle.changes") deleted, oracle $(cat "$LOG/$label.oracle.time")s, goport $(cat "$LOG/$label.goport.time")s)"
  else
    echo "$repo $label DIFF: ${fail[*]} (unported $unported; see $LOG/$label.*)"
  fi
}

# Same edit on both copies. The edited file gets the same mtime in both.
cmd_edit() {
  repo_config "$1"; local kind=$2 file
  case $kind in
    touch|body) file=$UP_FILE ;;
    api|err|fix) file=$API_FILE ;;
    *) echo "unknown edit $kind" >&2; exit 2 ;;
  esac
  [[ -n $file ]] || { echo "$1: no file for edit $kind" >&2; return 1; }
  local o=$BASE/oracle/$file
  case $kind in
    touch) touch "$o" ;;
    body) printf '\nvoid 0;\n' >> "$o" ;;
    api) printf '\nexport const goportApi = 1;\n' >> "$o" ;;
    err) printf '\nexport const goportErr: number = "x";\n' >> "$o" ;;
    fix) sed -i '/^export const goportErr: number = "x";$/d' "$o"; touch "$o" ;;
  esac
  cp -a "$o" "$BASE/goport/$file"
  echo "edit $1 $kind $file"
}

cmd_seq() {
  local repo=$1; shift
  local phases=("$@")
  [[ ${#phases[@]} -gt 0 ]] || phases=(cold)
  for phase in "${phases[@]}"; do
    case $phase in
      cold)
        cmd_init "$repo"
        cmd_step "$repo" s1-cold
        cmd_step "$repo" s2-uptodate ;;
      edits)
        cmd_edit "$repo" touch; cmd_step "$repo" s3-touch
        cmd_edit "$repo" body; cmd_step "$repo" s4-body
        cmd_edit "$repo" api; cmd_step "$repo" s5-api
        cmd_edit "$repo" err; cmd_step "$repo" s6-err
        cmd_step "$repo" s6-err-stop --stopBuildOnErrors
        cmd_edit "$repo" fix; cmd_step "$repo" s6b-fix
        cmd_step "$repo" s6c-uptodate ;;
      flags)
        cmd_step "$repo" s7-dry --dry
        cmd_step "$repo" s7-force --force
        cmd_step "$repo" s7-clean-dry --clean --dry
        cmd_step "$repo" s7-clean --clean
        cmd_step "$repo" s7-after-clean --singleThreaded ;;
      foreign)
        cmd_init "$repo" keep-buildinfo
        cmd_step "$repo" s8-foreign
        cmd_step "$repo" s8-uptodate ;;
      *) echo "unknown phase $phase" >&2; exit 2 ;;
    esac
  done
}

case ${1:-} in
  init) shift; cmd_init "$@" ;;
  step) shift; cmd_step "$@" ;;
  edit) shift; cmd_edit "$@" ;;
  seq) shift; cmd_seq "$@" ;;
  *) sed -n '2,24p' "$0"; exit 2 ;;
esac
