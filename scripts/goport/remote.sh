#!/usr/bin/env bash
# Remote measurement runners. zbook builds; alvin, cup2 and dbook run gates, corpus suites, sweeps and oracle checks.
# Each host keeps a mirror at the same absolute paths as zbook: this repo's tooling, target/project-inputs*,
# the target/continuation-r97-goport runners, oracle caches and default binaries, ~/.local/bin/tsgo-oracle and
# ~/.explore/repos/microsoft__typescript-go (see target/continuation-r97-goport/remote/*-manifest.txt).
#
# usage: remote.sh sync-bins <host> <dir>...  copy the top-level files of binary dirs (not deps/ or build/)
#        remote.sh sync-scripts <host>        copy repo scripts, tools, .git, runner scripts under target/, /tmp/port
#        remote.sh run <host> <command...>    run a command in the repo root with a login shell; output streams
#        remote.sh fetch <host> <dir>...      copy result dirs back to zbook; adds new files, never replaces one
# <host> is alvin, cup2, dbook-lan, "all" (sync-*: every host at the same time) or "auto" (first idle host).
# Host order is alvin, cup2, dbook-lan (REMOTE_HOSTS overrides it). Relative dirs are relative to the repo root.
set -uo pipefail
REPO=/home/theo/Code/sandbox/ts-rust
T=$REPO/target
read -ra HOSTS <<< "${REMOTE_HOSTS:-alvin cup2 dbook-lan}"
RS=(rsync -aH --mkpath --compress --compress-choice=zstd --info=progress2)

die() { echo "remote.sh: $*" >&2; exit 2; }
# Absolute path with symlinks kept, so it names the same place on both sides.
abs() { (cd "$REPO" && realpath -ms "$1"); }
# Never write into project inputs. Their measure/ output dirs are allowed (the sweep scripts write there).
guard() { [[ $1 != "$T"/project-inputs* || $1 == "$T"/project-inputs*/measure/?* ]] || die "refusing to write into project inputs: $1"; }
# First host in order whose repo path resolves to itself (else tools print other paths), with load under half its cores.
pick() {
  local h; for h in "${HOSTS[@]}"; do
    ssh "$h" "{ [ -x ~/.local/bin/zbook-paths ] || [ \"\$(realpath $REPO)\" = $REPO ]; } && awk -v n=\$(nproc) '{exit !(\$1 < n / 2)}' /proc/loadavg" && { echo "$h"; return; }
  done
  die "no idle host with a correct mirror in: ${HOSTS[*]}"
}
sync_bins() {
  local h=$1 d; shift
  for d in "$@"; do
    d=$(abs "$d"); [[ -d $d ]] || die "not a dir: $d"; guard "$d"
    "${RS[@]}" --exclude='*/' --exclude='*.d' --exclude='*.rlib' --exclude='.*' "$d/" "$h:$d/" || return
  done
}
# Tooling that changes between runs. Data (inputs, oracle caches, corpus cases, goldens) is mirrored once.
sync_scripts() {
  local h=$1 r=continuation-r97-goport f
  # .git is needed: gate.sh resolves --commit with git rev-parse. --delete only acts on the included paths.
  "${RS[@]}" --delete --filter='- /.git/worktrees/' --filter='- __pycache__/' --filter='+ /.git/***' \
    --filter='+ /UPSTREAM.json' --filter='+ /scripts/***' --filter='+ /tools/***' --filter='+ /crates/' --filter='+ /crates/*/' \
    --filter='+ /crates/*/scripts/***' --filter='- *' "$REPO/" "$h:$REPO/" || return
  # Runner scripts under target/. lsp_oracle.py is only in the goport-int7 and goport-ls worktrees.
  cd "$T" || return
  for f in $r/{tools-port,sample-f1,emit,typesyms,typesyms/scale,build-mode,corpus-full,corpus-variants}/*.{py,sh} \
      $r/{corpus-int3,corpus-p5,emit-corpus,compat,compat/p5-corpus,compat/all-configs-p5,all-configs}/*.{py,sh} \
      $r/{cli-complete,tsgo-bin}/audit-r3/*.{py,sh} worktrees/goport-{int7,ls}/scripts/goport project-inputs-extra/sweep-extra2.sh; do
    [[ -e $f ]] && echo "$f"
  done | "${RS[@]}" -r --exclude=__pycache__/ --files-from=- "$T/" "$h:$T/" || return
  # compat/p5-corpus and typesyms/scale call /tmp/port/treehash.py. /tmp is tmpfs on alvin and cup2.
  [[ ! -d /tmp/port ]] || "${RS[@]}" --include='*.py' --include='*.sh' --include=gate-allow.txt --exclude='*' /tmp/port/ "$h:/tmp/port/"
}
# A tty (when there is one) lets Ctrl-C stop the remote command too.
run() {
  local h=$1 cmd t=(); shift
  # GOPORT_PIN (scripts/upstream/pin.py) is passed on to the remote command.
  [[ -n ${GOPORT_PIN:-} ]] && set -- "export GOPORT_PIN=${GOPORT_PIN//[^0-9a-f]/};" "$@"
  printf -v cmd %q "$*"; [[ -t 0 && -t 1 ]] && t=(-t)
  # A host whose home layout differs from zbook (alvin: ~/Code links to ~/code) runs through its
  # ~/.local/bin/zbook-paths wrapper, a no-root mount namespace with zbook's paths and a private /tmp.
  # dbook logs in as user dbook but has a real /home/theo dir, so HOME=/home/theo gives zbook's ~ paths.
  exec ssh "${t[@]}" -o ServerAliveInterval=60 "$h" "cd $REPO || exit 2
    if [ -x ~/.local/bin/zbook-paths ]; then exec ~/.local/bin/zbook-paths bash -lc \"cd $REPO && \"$cmd; fi
    [ \"\$(pwd -P)\" = $REPO ] || { echo \"$h: $REPO resolves to \$(pwd -P); outputs would not match zbook\" >&2; exit 2; }
    exec env HOME=/home/theo bash -lc $cmd"
}
fetch() {
  local h=$1 d; shift
  for d in "$@"; do
    d=$(abs "$d"); guard "$d"
    case $d in "$T"/worktrees*) die "refusing to write into a worktree: $d" ;; "$T"/?*|/tmp/?*) ;; *) die "results live under $T or /tmp: $d" ;; esac
    "${RS[@]}" --ignore-existing "$h:$d/" "$d/" || return
  done
}
[[ $# -ge 2 ]] || { sed -n '7,12p' "$0"; exit 2; }
cmd=$1 host=$2; shift 2
case $cmd in sync-bins|sync-scripts|run|fetch) ;; *) die "unknown command $cmd" ;; esac
[[ $cmd == sync-scripts || $# -ge 1 ]] || die "$cmd needs more arguments"
[[ $host == auto ]] && { host=$(pick) || exit 2; }
if [[ $host == all ]]; then
  [[ $cmd == sync-* ]] || die "'all' only works with sync-bins and sync-scripts"
  pids=(); for h in "${HOSTS[@]}"; do "${cmd//-/_}" "$h" "$@" & pids+=($!); done
  rc=0; for p in "${pids[@]}"; do wait "$p" || rc=1; done; exit $rc
fi
"${cmd//-/_}" "$host" "$@"
