#!/usr/bin/env bash
# Candidate revisions of target/worktrees/checker-port: the steps root ran by hand for R113 to R125.
#
# usage: scripts/goport/candidate.sh <command> ... [--dry-run]
#   check <branch>         Scope of the <branch> diff against the batch allowedChangedFiles (and the two
#                          bind.py rules: no removed R96 file, additive ts_compiler lib.rs), and
#                          rustfmt --edition 2024 on each changed .rs file. Exit 1 on any problem.
#   open <rev> <branch> --hypothesis TEXT --change TEXT [--message TEXT] [--new-batch ID --origin TEXT]
#                          check, apply <branch> to the checkout (allowed paths, one commit, as root did
#                          for R121 to R125), fp.py and roster_fp.py, clone-revision.sh, an online
#                          `cargo fetch --locked` into the new pinned cargo home, and open_revision.py last
#                          (the only state write). Says when the roster run may be carried forward.
#   drive <rev> [--resume N]
#                          bind, the cloned drive (or drive-resume-N.sh), the raw pin and check-result.py,
#                          in systemd user unit ts-rust-drive-r<rev>. Log target/continuation-r<rev>-drive.log.
#   side <rev|label> [--checkout DIR] [--gate-host HOST|local]
#                          release bins in the shared target runtime/cargo-target, two bound runs, the
#                          full gate and the LSP oracle (default host dbook-lan), in unit
#                          ts-rust-side-<label>. Log target/continuation-r97-goport/quality-<label>-side.log.
#                          Each step is cached by source under evidence-cache/<key>/ and reused.
#   verdict-request <rev>  The request text for the auditor and the reviewer.
# --dry-run prints each command that writes and runs only the read-only checks.
#
# Monitors of drive and side grep only for the last log line. It is exactly one of
#   DRIVE DONE | DRIVE FAIL rc=<N> | SIDE DONE | SIDE FAIL rc=<N>
# (a timeout is "FAIL rc=124"). A killed unit prints nothing, so also stop when the unit is gone:
#   until grep -qE '^DRIVE (DONE|FAIL)' LOG || ! systemctl --user is-active -q UNIT; do sleep 30; done
set -euo pipefail

ROOT=/home/theo/Code/sandbox/ts-rust
R=$ROOT/target/continuation-r97-goport
SELF=$ROOT/scripts/goport/candidate.sh
EVIDENCE=${CANDIDATE_EVIDENCE:-$R/evidence-cache}  # tests point this at a copy
TARGET=$R/runtime/cargo-target                     # one warm target for candidate bins (gate.sh's default)
BINS=(goport goport_emit goport_typesyms goport_build tsgo)
LSP_BATTERIES=b1-inline,b1-query-core,b2-query-core,b1-hono,b2-hono,fourslash
CHECKER_PORT=$ROOT/target/worktrees/checker-port
cd "$ROOT"

usage() { sed -n '2,/^set -euo/p' "$SELF" | sed '$d'; exit 2; }
die() { echo "candidate.sh: $*" >&2; exit 1; }
say() { echo "== $*"; }
# need <condition text>: stops, except in a dry run, where an earlier step (open) would fix it.
need() { if [[ $DRY == 1 ]]; then echo "   (dry run; a real run stops here) $*"; else die "$*"; fi; }
# run <cmd...>: prints the command, then runs it unless --dry-run.
run() { printf '+'; printf ' %q' "$@"; printf '\n'; [[ $DRY == 1 ]] || "$@"; }
# run_sh <shell text>: the same for a command with redirects or pipes. fd 8 (the target lock) stays closed.
run_sh() { printf '+ %s\n' "$1"; [[ $DRY == 1 ]] || bash -c "set -euo pipefail; $1" 8>&-; }

# load_state: exports the saved state once; st <jq filter> reads it.
load_state() { STATE=$(mktemp /tmp/candidate-state.XXXXXX); trap 'rm -f "$STATE"' EXIT; node scripts/state.mjs export > "$STATE"; }
st() { jq -r "$1" "$STATE"; }

# fmt_clean <rev:path>: true when rustfmt --edition 2024 leaves that blob unchanged. Each file is formatted
# alone from stdin, so unchanged child modules do not count. A parse error counts as a problem.
fmt_clean() {
  local blob rc=0
  blob=$(mktemp /tmp/candidate-fmt.XXXXXX)
  git cat-file blob "$1" > "$blob"
  # shellcheck disable=SC2094 # both sides only read the file
  rustfmt --edition 2024 --emit stdout < "$blob" 2> /dev/null | cmp -s - "$blob" || rc=1
  rm -f "$blob"
  return $rc
}

# check_branch <branch>: problems of <branch> as the next source of the checkout, against its HEAD.
# Prints each problem and returns 1 when there is one.
check_branch() {
  local branch=$1 wt base sha prev_tree status path pat ok n=0 nrs=0 removed
  local -a allowed problems=()
  wt=$ROOT/$(st .batch.checkout)
  base=$(git -C "$wt" rev-parse HEAD)
  sha=$(git rev-parse --verify --quiet "$branch^{commit}") || die "unknown branch or commit: $branch"
  mapfile -t allowed < <(st '.batch.allowedChangedFiles[]')
  prev_tree=$ROOT/$(jq -r .previousSourceTree.checkout \
    "$ROOT/target/continuation-r$(st .batch.recoveryRevision)-runtime-env/preparation-manifest.json")
  say "check $branch ${sha:0:9} against $(st .batch.checkout) ${base:0:9}; allowed: ${allowed[*]}"
  while IFS= read -r -d '' status && IFS= read -r -d '' path; do
    n=$((n + 1)) ok=0
    # shellcheck disable=SC2053 # allowedChangedFiles are globs, matched like bind.py's fnmatch
    for pat in "${allowed[@]}"; do if [[ $path == $pat ]]; then ok=1; fi; done
    ((ok)) || problems+=("outside allowedChangedFiles: $path")
    if [[ $status == D ]]; then
      [[ ! -e $prev_tree/$path ]] || problems+=("removes $path, an R96 source file (bind.py refuses removals)")
      continue
    fi
    if [[ $path == *.rs ]]; then
      nrs=$((nrs + 1))
      fmt_clean "$sha:$path" || problems+=("rustfmt --edition 2024 would change $path")
    fi
    if [[ $path == crates/ts_compiler/src/lib.rs ]]; then
      removed=$(diff "$prev_tree/$path" <(git cat-file blob "$sha:$path") | grep -c '^<' || true)
      ((removed == 0)) || problems+=("$path removes $removed line(s) of the R96 file (bind.py needs an additive change)")
    fi
  done < <(git diff --no-renames --name-status -z "$base" "$sha" -- crates Cargo.toml Cargo.lock)
  git diff --quiet "$base" "$sha" -- Cargo.lock || echo "   Cargo.lock changes: open seeds the new pinned cargo home online"
  if ((${#problems[@]})); then
    printf '   PROBLEM %s\n' "${problems[@]}"
    echo "check FAIL: ${#problems[@]} problem(s) in $n changed path(s)"
    return 1
  fi
  echo "check OK: $n changed path(s) in scope, $nrs .rs file(s) rustfmt clean"
}

# cmd_open <rev> <branch>: makes <branch> the source of R<rev> and opens R<rev>. The state is written last,
# so a failed step leaves no revision row.
cmd_open() {
  local rev=$1 branch=$2 last old_batch new_batch wt T base sha patch msg commit fp roster prev dirty p
  local -a allowed specs=() orv
  [[ -n $HYP && -n $CHANGE ]] || die "open needs --hypothesis and --change"
  [[ -z $NEW_BATCH || -n $ORIGIN ]] || die "--new-batch needs --origin"
  last=$(st '.batch.recoveryHistory[-1].revision')
  ((rev == last + 1)) || die "R$rev is not the next revision (R$((last + 1)))"
  old_batch=$(st .batch.id) new_batch=${NEW_BATCH:-$(st .batch.id)}
  [[ -n $NEW_BATCH || $(st .batch.compilerAccepted) != true ]] || die "batch $old_batch is accepted; pass --new-batch ID --origin TEXT"
  wt=$ROOT/$(st .batch.checkout) T=$ROOT/target/continuation-r$rev
  dirty=$(git -C "$wt" status --porcelain | grep -v '^?? crates/ts_goport/CANDIDATE.md$' || true)
  [[ -z $dirty ]] || die "$wt has changes besides CANDIDATE.md:"$'\n'"$dirty"
  [[ ! -e $T-drive.sh && ! -e $T-runtime-env ]] || die "R$rev pipeline files exist; remove $T-* first"
  check_branch "$branch" || die "check failed; nothing was changed"

  sha=$(git rev-parse "$branch^{commit}") base=$(git -C "$wt" rev-parse HEAD)
  mapfile -t allowed < <(st '.batch.allowedChangedFiles[]')
  for p in "${allowed[@]}"; do specs+=(":(glob)$p"); done
  if git diff --quiet "$base" "$sha" -- "${specs[@]}"; then
    say "$(st .batch.checkout) already equals $branch in the allowed paths; no commit"
    commit=$(git -C "$wt" rev-parse --short=9 HEAD)
  else
    say "apply $branch to $(st .batch.checkout):$(git diff --shortstat "$base" "$sha" -- "${specs[@]}")"
    patch=/tmp/candidate-r$rev.patch msg=$MESSAGE
    [[ -n $msg ]] || printf -v msg 'chore(goport): R%s source from %s %s\n\n%s' "$rev" "$branch" "${sha:0:9}" "$CHANGE"
    run_sh "git diff --binary $base $sha -- $(printf '%q ' "${specs[@]}")> $patch"
    run git -C "$wt" apply --index "$patch"
    run git -C "$wt" commit -q -m "$msg"
    commit='<new HEAD>'
  fi
  if [[ $commit == '<'* && $DRY == 1 ]]; then
    fp='<fp.py after the apply>'
    roster='<roster_fp.py after the apply>'
    if git diff --quiet "$base" "$sha" -- "${specs[@]}" ':(exclude,glob)crates/ts_goport/**'; then
      roster=$(python3 scripts/goport/roster_fp.py "$wt" | cut -d' ' -f1)
    fi
  else
    git -C "$wt" diff --quiet "$sha" HEAD -- crates Cargo.toml Cargo.lock || die "crates of $wt differ from $branch"
    commit=$(git -C "$wt" rev-parse --short=9 HEAD)
    fp=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
    roster=$(python3 scripts/goport/roster_fp.py "$wt" | cut -d' ' -f1)
  fi
  say "R$rev commit $commit, source fingerprint $fp, roster fingerprint $roster"

  orv=(python3 scripts/goport/open_revision.py --revision "$rev" --fingerprint "$fp" --commit "$commit"
    --hypothesis "$HYP" --change "$CHANGE")
  [[ -z $NEW_BATCH ]] || orv+=(--new-batch "$NEW_BATCH" --origin "$ORIGIN")
  if [[ $fp != '<'* ]]; then
    say "open_revision.py checks (--dry-run, no write)"
    if [[ $DRY == 1 ]]; then "${orv[@]}" --dry-run; else "${orv[@]}" --dry-run > /dev/null; fi
  fi
  run scripts/goport/clone-revision.sh "$last" "$rev" "$old_batch" "$new_batch"
  run_sh "env -u CARGO_NET_OFFLINE CARGO_HOME=$T-runtime-env/cargo-home cargo fetch --locked --manifest-path $wt/Cargo.toml > $T-runtime-env/cargo-fetch.log 2>&1"
  run "${orv[@]}"

  prev=$(st '[.batch.recoveryHistory[] | select((.status // "") | startswith("full_measured")) | select(.rosterFingerprint)]
    | last // empty | "\(.revision) \(.rosterFingerprint)"')
  if [[ -n $prev && ${prev#* } == "$roster" ]]; then
    say "roster fingerprint equals R${prev%% *}: the protected roster run may be carried forward"
    echo "   (accept_revision.py --carry-from ${prev%% *}); drive is not needed"
  else
    say "roster run needed (${prev:+R${prev%% *} roster ${prev#* }}${prev:-no measured revision has a rosterFingerprint}): $SELF drive $rev"
  fi
  say "then: $SELF side $rev; after both: $SELF verdict-request $rev"
  say "commit the state: git add docs && git commit"
  [[ -z $NEW_BATCH ]] || say "add $NEW_BATCH to the rule extension list in docs/typechecker-accountability.md"
}

# pass_compare <rev>: PASS names of the R<rev> check result against the latest earlier one.
pass_compare() {
  local rev=$1 p=$(($1 - 1))
  while ((p > rev - 10)) && [[ ! -e $ROOT/target/continuation-r$p-check-result.json ]]; do p=$((p - 1)); done
  python3 - "$ROOT/target/continuation-r$rev-check-result.json" "$ROOT/target/continuation-r$p-check-result.json" "$rev" "$p" <<'PY'
import json, os, sys
def passes(path):
    d = json.load(open(path))
    return ({(e['harness'], e['name']) for e in d['versusFullBaseline']['exactLedger'] if e['current']['status'] == 'PASS'}
            | {(e['harness'], e['name']) for e in d['addedNames'] if e['status'] == 'PASS'})
cur, old = passes(sys.argv[1]), passes(sys.argv[2]) if os.path.exists(sys.argv[2]) else None
if old is None:
    print(f'R{sys.argv[3]} PASS {len(cur)}; no earlier check result to compare')
else:
    print(f'R{sys.argv[3]} PASS {len(cur)}; against R{sys.argv[4]} ({len(old)} PASS): {len(old - cur)} lost, {len(cur - old)} new')
    for h, n in sorted(old - cur)[:20]:
        print(f'  lost {h} {n}')
PY
}

# cmd_drive <rev>: starts drive_unit in systemd user unit ts-rust-drive-r<rev>[-resume-N].
cmd_drive() {
  local rev=$1 T=$ROOT/target/continuation-r$1 unit=ts-rust-drive-r$1 log script
  log=$T-drive.log script=$T-drive.sh
  if [[ -n $RESUME ]]; then log=$T-drive-resume-$RESUME.log script=$T-drive-resume-$RESUME.sh unit+=-resume-$RESUME; fi
  [[ $(st .batch.recoveryRevision) == "$rev" && $(st .batch.sourceBindingStatus) == SOURCE_BOUND ]] ||
    need "the state is at R$(st .batch.recoveryRevision), not bound at R$rev; run open first"
  [[ -f $script ]] || need "missing $script"
  [[ ! -e $log ]] || die "$log exists; keep it (rename to -interrupted-N.log), write $T-drive-resume-N.sh, use --resume N"
  ! systemctl --user is-active -q "$unit" || die "$unit is running"
  say "drive R$rev in unit $unit, log $log"
  run systemd-run --user --collect --unit="$unit" --working-directory="$ROOT" --setenv=PATH="$PATH" --setenv=HOME="$HOME" \
    bash -c "exec bash $SELF _drive-unit $rev ${RESUME:-0} >> $log 2>&1"
  if [[ $DRY == 1 ]]; then say "the unit runs:"; drive_unit "$rev" "${RESUME:-0}"; fi
  echo "monitor: until grep -qE '^DRIVE (DONE|FAIL)' $log || ! systemctl --user is-active -q $unit; do sleep 30; done; tail -4 $log"
}

# drive_unit <rev> <resume N, or 0>: body of the drive unit. Binds once, runs the drive, pins the raw result in
# check-result.py (clone-revision.sh pin-raw) and converts it. Last log line: DRIVE DONE or DRIVE FAIL rc=<N>.
drive_unit() {
  local rev=$1 T=$ROOT/target/continuation-r$1 script=$ROOT/target/continuation-r$1-drive.sh
  [[ $2 == 0 ]] || script=$T-drive-resume-$2.sh
  [[ $DRY == 1 ]] || trap 'rc=$?; if ((rc)); then echo "DRIVE FAIL rc=$rc"; else echo "DRIVE DONE"; fi' EXIT
  [[ -e $T-binding.json ]] || run_sh "python3 $T-bind.py > /dev/null"
  run python3 "$T-require-bound.py"
  run bash "$script"
  if [[ -e $T-check-result.json ]]; then say "$T-check-result.json exists"; else
    run scripts/goport/clone-revision.sh pin-raw "$rev"
    run python3 "$T-check-result.py"
  fi
  [[ $DRY == 1 ]] || pass_compare "$rev" || echo "(the PASS name compare failed; the drive result stands)"
}

# evidence_key <checkout> [pin]: cache key of the bins and their evidence. It covers the committed crates
# tree, Cargo.toml and Cargo.lock, each dirty or untracked file under them (except the CANDIDATE.md marker,
# as in bound2.sh), the Go pin (default: UPSTREAM.json current) and the build profile.
evidence_key() {
  local wt=$1 pin=${2:-} line
  [[ -n $pin ]] || pin=$(jq -r .current "$ROOT/UPSTREAM.json")
  {
    git -C "$wt" rev-parse HEAD:crates HEAD:Cargo.toml HEAD:Cargo.lock
    git -C "$wt" status --porcelain --untracked-files=all -- crates Cargo.toml Cargo.lock | while IFS= read -r line; do
      [[ $line != '?? crates/ts_goport/CANDIDATE.md' ]] || continue
      echo "$line"
      if [[ -f $wt/${line:3} ]]; then sha256sum < "$wt/${line:3}"; fi
    done
    echo "pin=$pin profile=release toolchain=$(rustc --version 2>/dev/null) incremental=0"
  } | sha256sum | cut -c1-16
}

# cmd_side <rev|label>: starts side_unit in systemd user unit ts-rust-side-<label>.
cmd_side() {
  local label=$1 wt pin unit log
  if [[ $label =~ ^[0-9]+$ ]]; then label=r$label; fi
  [[ $label =~ ^[A-Za-z0-9._-]+$ ]] || die "label must match [A-Za-z0-9._-]+"
  wt=$(realpath "${CHECKOUT:-$ROOT/$(st .batch.checkout)}")
  pin=$(st '.batch.upstreamPin.to // empty')
  unit=ts-rust-side-$label log=$R/quality-$label-side.log
  [[ ! -e $log ]] || die "$log exists; rename it first (finished steps stay cached)"
  ! systemctl --user is-active -q "$unit" || die "$unit is running"
  local -a env=(--setenv=PATH="$PATH" --setenv=HOME="$HOME")
  [[ -z ${SSH_AUTH_SOCK:-} ]] || env+=(--setenv=SSH_AUTH_SOCK="$SSH_AUTH_SOCK")
  say "side $label in unit $unit, log $log"
  run systemd-run --user --collect --unit="$unit" --working-directory="$ROOT" "${env[@]}" \
    bash -c "exec bash $SELF _side-unit $label $wt ${pin:--} $HOST >> $log 2>&1"
  if [[ $DRY == 1 ]]; then say "the unit runs:"; side_unit "$label" "$wt" "${pin:--}" "$HOST"; fi
  echo "monitor: until grep -qE '^SIDE (DONE|FAIL)' $log || ! systemctl --user is-active -q $unit; do sleep 30; done; tail -8 $log"
}

# free_name <dir> <name>: <name>, or <name>-2, -3, ... when <dir>/<name> exists (gate labels are never reused).
free_name() { local n=$2 i=2; while [[ -e $1/$n ]]; do n=$2-$i i=$((i + 1)); done; echo "$n"; }

# side_unit <label> <checkout> <pin|-> <host|local>: body of the side unit. Each finished step is a file in
# the cache dir (bins/, bound.json, gate.json, lsp.json) and is reused. Last log line: SIDE DONE or
# SIDE FAIL rc=<N>.
side_unit() {
  local label=$1 wt=$2 pin=${3#-} host=$4 key C B commit fp n r gl ll rc oracle lock synced=0 g l gate_fail=''
  local -a pinexec=()
  [[ $DRY == 1 ]] || trap 'rc=$?; if ((rc)); then echo "SIDE FAIL rc=$rc"; else echo "SIDE DONE"; fi' EXIT
  [[ -z $pin ]] || pinexec=(env GOPORT_PIN="$pin" python3 "$ROOT/scripts/upstream/pin.py" exec --)
  key=$(evidence_key "$wt" "$pin") C=$EVIDENCE/$key B=$EVIDENCE/$key/bins
  commit=$(git -C "$wt" rev-parse HEAD) lock=/tmp/goport-remote-${host%-lan}.lock
  say "$(date -u +%FT%TZ) side $label: $wt ${commit:0:9}, crates tree $(git -C "$wt" rev-parse HEAD:crates | cut -c1-12), pin ${pin:-current}, evidence $C"
  run mkdir -p "$C"

  # Bins (release profile). The target lock keeps another side run from replacing the target's bins
  # between this build and the copy.
  if [[ -f $B/bins.sha256 ]]; then say "reuse bins $B (built from $(cat "$B/COMMIT"))"; else
    say "$(date -u +%FT%TZ) build release bins in $TARGET"
    if [[ $DRY == 0 ]]; then exec 8> /tmp/ts-rust-candidate-target.lock; flock 8; fi
    # Evidence bins: the shipped toolchain (not the nightly edit-loop default) and no incremental cache.
    run_sh "cd $wt && TS_CARGO_NIGHTLY=0 TS_CARGO_INCREMENTAL=0 TS_CARGO_LOCK_ID=candidate-side TS_CARGO_JOBS=12 TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR=$TARGET $ROOT/scripts/run-cargo-capped.sh build --locked --release -p ts_goport ${BINS[*]/#/--bin } > $C/build.log 2>&1"
    run_sh "rm -rf $B.new && mkdir $B.new && cd $TARGET/release && cp ${BINS[*]} $B.new/ && cd $B.new && sha256sum ${BINS[*]} > bins.sha256 && echo $commit > COMMIT"
    if [[ $DRY == 0 ]]; then
      exec 8>&-
      [[ $(evidence_key "$wt" "$pin") == "$key" ]] || die "the source changed during the build; $B.new is not cached"
    fi
    run mv "$B.new" "$B"
  fi

  # Bound runs. bound2.sh measures only the checker-port checkout and records its commit and fingerprint.
  if [[ $wt != "$CHECKER_PORT" ]]; then say "skip bound runs: bound2.sh measures only $CHECKER_PORT"; else
    fp=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
    if [[ -f $C/bound.json && $(jq -r .sourceFingerprint "$C/bound.json") == "$fp" ]]; then
      say "reuse bound runs $(jq -r '.rounds | join(" ")' "$C/bound.json")"
    else
      n=0
      for r in "$R"/measure/r*; do r=${r##*/r}; if [[ $r =~ ^[0-9]+$ ]] && ((r > n)); then n=$r; fi; done
      n=r$((n + 1))
      for r in "$n" "${n}b"; do
        say "$(date -u +%FT%TZ) bound run $r"
        run_sh "GOPORT_REL=$B ${pinexec[*]} bash scripts/goport/bound2.sh $r > $C/bound-$r.log 2>&1"
      done
      if [[ $DRY == 0 ]]; then
        ! grep -HE 'DIFF|INCOMPLETE' "$R/measure/$n"/summary-*.txt "$R/measure/${n}b"/summary-*.txt || die "bound runs $n, ${n}b: not all MATCH"
        for r in query hono Q-E1 Q-E2 Q-E3 Q-E4 Q-E5 H-E1; do
          cmp -s "$R/measure/$n/$r.out" "$R/measure/${n}b/$r.out" || die "$r differs between $n and ${n}b"
        done
        jq -n --arg fp "$fp" --arg c "$commit" --arg a "$n" --arg b "${n}b" --arg m "$R/measure" \
          '{sourceFingerprint: $fp, commit: $c, rounds: [$a, $b], manifests: [$m + "/" + $a + "/manifest.json", $m + "/" + $b + "/manifest.json"]}' > "$C/bound.json"
      fi
    fi
  fi

  # Remote runs: pin, scripts and bins go to the host first, once.
  remote_sync() {
    [[ $host != local && $synced == 0 ]] || return 0
    synced=1
    [[ -z $pin ]] || run_sh "scripts/goport/remote.sh sync-pin $host $pin >> $C/sync.log 2>&1"
    run_sh "scripts/goport/remote.sh sync-scripts $host >> $C/sync.log 2>&1"
    run_sh "scripts/goport/remote.sh sync-bins $host $B >> $C/sync.log 2>&1"
  }
  # on_host <GOPORT_PIN value> <command text> <log>: runs the command in the repo root, on zbook or under
  # the host lock.
  on_host() {
    if [[ $host == local ]]; then run_sh "export GOPORT_PIN=$1; ($2) < /dev/null > $3 2>&1"
    else run_sh "flock $lock env GOPORT_PIN=$1 scripts/goport/remote.sh run $host $(printf %q "$2") < /dev/null > $3 2>&1"; fi
  }

  # Gate (full). Only a PASS is cached.
  if [[ -f $C/gate.json ]]; then say "reuse gate $(jq -r '"\(.label) \(.verdict)"' "$C/gate.json")"; else
    gl=$(free_name "$R/compat/gate" "$label-full") rc=0
    remote_sync
    say "$(date -u +%FT%TZ) gate $gl on $host"
    on_host "$pin" "bash scripts/goport/gate.sh $gl --full --bins $B --commit $commit" "$C/gate-$gl.log" || rc=$?
    [[ $host == local ]] || run_sh "scripts/goport/remote.sh fetch $host $R/compat/gate/$gl >> $C/sync.log 2>&1"
    if [[ $DRY == 0 ]]; then
      tail -n 3 "$C/gate-$gl.log"
      [[ -f $R/compat/gate/$gl/manifest.json ]] || die "gate $gl rc $rc and no manifest (log $C/gate-$gl.log)"
      # A FAIL is recorded in gate-fail.json (not reused) with the failing items, and the other steps
      # still run, so the verdict request has all the evidence. The unit ends SIDE FAIL.
      g=$C/gate.json; ((rc == 0)) || { g=$C/gate-fail.json; gate_fail="gate $gl rc $rc (log $C/gate-$gl.log)"; }
      jq --arg l "$gl" --arg m "$R/compat/gate/$gl/manifest.json" --arg s "$(sha256sum < "$R/compat/gate/$gl/manifest.json" | cut -c1-64)" --arg h "$host" \
        '{label: $l, manifest: $m, sha256: $s, host: $h, verdict, commit, upstreamPin,
          counts: ([.results[].status] | group_by(.) | map({(.[0]): length}) | add),
          failing: [.results[] | select(.status == "FAIL") | {id, detail}]}' \
        "$R/compat/gate/$gl/manifest.json" > "$g"
    fi
  fi

  # LSP oracle (the batteries of the R121 to R125 side scripts).
  if [[ -f $C/lsp.json ]]; then say "reuse LSP oracle $(jq -r .label "$C/lsp.json")"; else
    ll=$(free_name "$R/ls-oracle/battery/results" "lsp-$label") rc=0
    oracle=$(python3 scripts/upstream/pin.py path oracle ${pin:+"$pin"})
    remote_sync
    say "$(date -u +%FT%TZ) LSP oracle $ll on $host"
    l="cd target/worktrees/goport-int7 && python3 scripts/goport/lsp_oracle.py check --out-root $R/ls-oracle/battery"
    l+=" --battery $LSP_BATTERIES --goport $B/tsgo --oracle $oracle --label $ll --jobs 12"
    on_host "" "$l" "$C/lsp-$ll.log" || rc=$?  # the oracle path carries the pin
    [[ $host == local ]] || run_sh "scripts/goport/remote.sh fetch $host $R/ls-oracle/battery/results/$ll >> $C/sync.log 2>&1"
    if [[ $DRY == 0 ]]; then
      ((rc == 0)) || die "LSP oracle $ll rc $rc (log $C/lsp-$ll.log)"
      python3 - "$R/ls-oracle/battery/results/$ll/summary.json" "$ll" > "$C/lsp.json" <<'PY'
import json, sys
b = json.load(open(sys.argv[1]))['batteries'].values()
count = lambda k: sum(x['classes'].get(k, 0) for x in b)
print(json.dumps({'label': sys.argv[2], 'summary': sys.argv[1].replace('.json', '.md'), 'requests': sum(x['requests'] for x in b),
                  'diff': count('diff'), 'goportError': count('goport_error'), 'crash': count('crash') + sum(x['crashExits'] for x in b),
                  'timeout': count('timeout')}))
PY
    fi
  fi

  # Quality on the checkout: rustfmt and clippy (R114 and R124 were refused for quality alone, and the
  # roster carry-forward rule still requires quality on the current source). Fingerprint before and after.
  if [[ -f $C/quality.json ]]; then say "reuse quality $(jq -c . "$C/quality.json")"; else
    say "$(date -u +%FT%TZ) quality: rustfmt and clippy"
    if [[ $DRY == 0 ]]; then
      local fpa fpb fmt=0 cl=0 warn
      fpb=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
      (cd "$wt" && rustfmt --edition 2024 --check $(git ls-files 'crates/ts_goport/**/*.rs') > "$C/rustfmt.log" 2>&1) || fmt=$?
      (cd "$wt" && TS_CARGO_LOCK_ID=candidate-side TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR=$R/runtime/cargo-r113-clippy \
        "$ROOT/scripts/run-cargo-capped.sh" clippy --locked -p ts_goport --all-targets > "$C/clippy.log" 2>&1) || cl=$?
      fpa=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
      warn=$(grep -E '^(warning|error)' -A4 "$C/clippy.log" | grep -c -- '--> crates/ts_goport' || true)
      jq -n --arg fp "$fpa" --argjson fmt "$fmt" --argjson cl "$cl" --argjson w "$warn" --argjson same "$([[ $fpa == "$fpb" ]] && echo true || echo false)" \
        '{sourceFingerprint: $fp, rustfmtExit: $fmt, clippyExit: $cl, tsGoportWarnings: $w, fingerprintUnchanged: $same}' > "$C/quality.json"
      [[ $fmt == 0 && $cl == 0 && $warn == 0 && $fpa == "$fpb" ]] || { rm -f "$C/quality.json.ok"; gate_fail="${gate_fail:+$gate_fail; }quality: rustfmt $fmt, clippy $cl, warnings $warn"; }
    fi
  fi

  say "$(date -u +%FT%TZ) evidence $C"
  for g in bound gate gate-fail lsp quality; do if [[ -f $C/$g.json ]]; then echo "   $g: $(jq -c 'del(.manifests)' "$C/$g.json")"; fi; done
  [[ -z $gate_fail ]] || die "$gate_fail"
}

# cmd_verdict <rev>: prints the verdict request texts from the state, the check result and the evidence
# cache. Exits 1 after printing when evidence is missing.
cmd_verdict() {
  local rev=$1 wt key compare=''
  [[ $(st .batch.recoveryRevision) == "$rev" ]] || die "the batch is at R$(st .batch.recoveryRevision), not R$rev"
  wt=$ROOT/$(st .batch.checkout)
  key=$(evidence_key "$wt" "$(st '.batch.upstreamPin.to // empty')")
  [[ ! -e $ROOT/target/continuation-r$rev-check-result.json ]] || compare=$(pass_compare "$rev" | head -1)
  python3 - "$STATE" "$rev" "$EVIDENCE/$key" "$compare" <<'PY'
import hashlib, json, os, subprocess, sys
ROOT = '/home/theo/Code/sandbox/ts-rust'
s, rev, cache, compare = json.load(open(sys.argv[1])), int(sys.argv[2]), sys.argv[3], sys.argv[4]
b = s['batch']
row, rows = b['recoveryHistory'][-1], b['recoveryHistory'][:-1]
wt = os.path.join(ROOT, b['checkout'])
git = lambda *a: subprocess.check_output(['git', '-C', wt, *a], text=True).strip()
sha = lambda p: hashlib.sha256(open(os.path.join(ROOT, p), 'rb').read()).hexdigest()
load = lambda p: json.load(open(p)) if os.path.exists(p) else None
rel = lambda p: p.replace(ROOT + '/', '')
missing, ev = [], []
T = f'target/continuation-r{rev}'
cr, raw = f'{T}-check-result.json', f'{T}-full-result.json'
prev = next((r for r in reversed(rows) if (r.get('status') or '').startswith('full_measured') and r.get('rosterFingerprint')), None)
if os.path.exists(os.path.join(ROOT, cr)):
    c = json.load(open(os.path.join(ROOT, cr)))['current']
    result = f'check-format result {cr} sha256 {sha(cr)} (raw {raw} sha256 {sha(raw)})'
    ev.append(f"Full regression: {c['tests']:,} tests, {c['PASS']:,} PASS, {c['FAIL']:,} FAIL, {c['ABSENT']} ABSENT, {c['UNRUN']} UNRUN; "
              f"name-level compare: {compare or 'none'}.")
    for log in sorted(f for f in os.listdir(f'{ROOT}/target') if f.startswith(f'continuation-r{rev}-drive') and f.endswith('.log')):
        last = open(f'{ROOT}/target/{log}').read().rstrip().splitlines()[-1:]
        ev.append(f"Drive log target/{log}: last line {last[0] if last else '(empty)'}.")
    counts = [f"{m} exact {load(f'{ROOT}/{T}-current-source-corpus/{m}-comparison.json')['counts']['after']['exact']}"
              for m in ('diagnostics', 'semantic') if os.path.exists(f'{ROOT}/{T}-current-source-corpus/{m}-comparison.json')]
    ev.append(f"Corpus ({T}-current-source-corpus/): {', '.join(counts) or 'MISSING'}.")
    if len(counts) < 2:
        missing.append('corpus comparisons')
elif prev and prev['rosterFingerprint'] == row.get('rosterFingerprint'):
    p = prev['revision']
    pcr = f'target/continuation-r{p}-check-result.json'
    result = f'protected roster carried forward from R{p} (rosterFingerprint {prev["rosterFingerprint"]} equal), check-format result {pcr} sha256 {sha(pcr)}'
else:
    result, missing = f'check-format result {cr}: MISSING', missing + [cr]
bound, gate, lsp, quality = (load(f'{cache}/{k}.json') for k in ('bound', 'gate', 'lsp', 'quality'))
gate = gate or load(f'{cache}/gate-fail.json')
bins = f'{cache}/bins'
if bound:
    ev.append(f"Bound runs {' and '.join(bound['rounds'])} ({', '.join(map(rel, bound['manifests']))}): all MATCH, the two runs identical; "
              f"bins {rel(bins)} (bins.sha256 there, release profile).")
else:
    missing.append('bound runs (candidate.sh side)')
if gate:
    same = '' if gate['commit'] == git('rev-parse', 'HEAD') else f", run on commit {gate['commit'][:9]} with the same crates tree"
    ev.append(f"Gate {gate['label']} ({gate['host']}{', pin ' + gate['upstreamPin'] if gate.get('upstreamPin') else ''}), manifest {rel(gate['manifest'])} "
              f"sha256 {gate['sha256']}: {gate['verdict']}, " + ', '.join(f'{gate["counts"][k]:,} {k}' for k in ('MATCH', 'ALLOWED', 'FAIL') if k in gate['counts']) + f'{same}.')
else:
    missing.append('gate (candidate.sh side)')
if lsp:
    ev.append(f"LSP oracle {lsp['label']} ({rel(lsp['summary'])}): {lsp['requests']:,} requests, {lsp['diff']} diff, {lsp['goportError']} goport_error, "
              f"{lsp['crash']} crash, {lsp['timeout']} timeout.")
else:
    missing.append('LSP oracle (candidate.sh side)')
if gate and gate.get('failing'):
    ev.append('Gate FAIL items: ' + '; '.join(f"{f['id']}: {f['detail']}" for f in gate['failing']) + '.')
if quality:
    ev.append(f"Quality on the source: rustfmt exit {quality['rustfmtExit']}, clippy exit {quality['clippyExit']}, "
              f"{quality['tsGoportWarnings']} ts_goport warnings, fingerprint unchanged {quality['fingerprintUnchanged']}.")
else:
    missing.append('quality: rustfmt and clippy (candidate.sh side)')
pin = (b.get('upstreamPin') or {}).get('to')
head = (f"Batch {b['id']}, revision {rev}, source fingerprint {b['sourceFingerprint']} "
        f"({b['checkout']} commit {b['commit']}, crates tree {git('rev-parse', 'HEAD:crates')[:12]}; roster fingerprint {row.get('rosterFingerprint') or 'not recorded'}), "
        f"{result}." + (f' Go pin {pin} (GOPORT_PIN for every Go comparison).' if pin else ''))
evidence = '\n'.join(f'- {e}' for e in ev)
ask = 'Please check the state and files and reply with VERDICT: PASS or STOP naming the batch, fingerprint and check sha.'
base = next((r.get('commit') for r in reversed(rows) if r.get('commit')), None)
diff = git('diff', '--shortstat', base, 'HEAD', '--', 'crates', 'Cargo.toml', 'Cargo.lock') if base else 'unknown'
outside = git('diff', '--name-only', base, 'HEAD', '--', 'crates', 'Cargo.toml', 'Cargo.lock', ':(exclude)crates/ts_goport').split() if base else []
for role, key in (('audit_accepted_roster', 'auditor'), ('independent_reviewer', 'reviewer')):
    print(f"===== to {b[key]['agent']} ({role})")
    print(f'Root: verdict request for R{rev} (role {role}). {head}\n')
    if key == 'reviewer':
        print(f"Change: {(row.get('change') or '').rstrip('.')} (git diff {base}..{b['commit']}:{diff}; outside crates/ts_goport: {', '.join(outside) or 'none'}).")
        print(f"Hypothesis: {row.get('hypothesis')}\n")
    print(f'Evidence:\n{evidence}')
    if key == 'reviewer':
        print('Please review the complete change against pinned Go (callers, caches, recursion, diagnostics, negative cases, '
              'repeat behavior), check the evidence, and reply with VERDICT: PASS or STOP naming the batch, fingerprint and check sha.\n')
    else:
        print(ask + '\n')
if missing:
    sys.exit('MISSING: ' + '; '.join(missing))
PY
}

DRY=0 HYP='' CHANGE='' MESSAGE='' NEW_BATCH='' ORIGIN='' RESUME='' CHECKOUT='' HOST=dbook-lan
args=()
while (($#)); do
  case $1 in
    --dry-run) DRY=1; shift ;;
    --hypothesis) HYP=${2:?--hypothesis needs a value}; shift 2 ;;
    --change) CHANGE=${2:?--change needs a value}; shift 2 ;;
    --message) MESSAGE=${2:?--message needs a value}; shift 2 ;;
    --new-batch) NEW_BATCH=${2:?--new-batch needs a value}; shift 2 ;;
    --origin) ORIGIN=${2:?--origin needs a value}; shift 2 ;;
    --resume) RESUME=${2:?--resume needs a value}; shift 2 ;;
    --checkout) CHECKOUT=${2:?--checkout needs a value}; shift 2 ;;
    --gate-host) HOST=${2:?--gate-host needs a value}; shift 2 ;;
    --*) die "unknown option $1" ;;
    *) args+=("$1"); shift ;;
  esac
done
set -- "${args[@]}"
cmd=${1:-}
(($#)) && shift
case $cmd:$# in
  check:1) load_state; check_branch "$1" ;;
  open:2) load_state; cmd_open "$@" ;;
  drive:1) load_state; cmd_drive "$1" ;;
  side:1) load_state; cmd_side "$1" ;;
  verdict-request:1) load_state; cmd_verdict "$1" ;;
  _drive-unit:2) drive_unit "$@"; exit 0 ;;
  _side-unit:4) side_unit "$@"; exit 0 ;;
  *) usage ;;
esac
