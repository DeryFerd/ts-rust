#!/usr/bin/env bash
# Candidate revisions of target/worktrees/checker-port. The protected set is goport's own tests and the
# gate items (docs/typechecker-accountability.md, "Protected set"); the legacy roster drive is retired.
#
# usage: scripts/goport/candidate.sh <command> ... [--dry-run]
#   check <branch>         Scope of the <branch> diff against the allowedChangedFiles of the revision (the
#                          batch's, or a new goport batch's when the batch is accepted or with --new-batch),
#                          and rustfmt --edition 2024 on each changed .rs file. Exit 1 on any problem.
#   open <rev> <branch> --hypothesis TEXT --change TEXT [--message TEXT] [--new-batch ID --origin TEXT]
#                          check, apply <branch> to the checkout (paths in scope, one commit), fp.py, and
#                          open_revision.py last (the only state write). A new batch has protectedSet goport.
#   side <rev|label> [--checkout DIR] [--gate-host HOST|local] [--name-map TSV]
#                          In systemd user unit ts-rust-side-<label>, log
#                          target/continuation-r97-goport/quality-<label>-side.log: release bins in the
#                          shared target runtime/cargo-target; goport tests (build-goport-tests.sh,
#                          goport-tests.sh, compare-tests.py against the base results; --name-map for moved
#                          or renamed tests); two bound runs; the full gate and gate-compare.py against the
#                          base gate manifest; the LSP oracle (default host dbook-lan); rustfmt and clippy.
#                          The base is the last accepted revision (open_revision.py --base). Each step is
#                          cached by source under evidence-cache/<key>/ and reused.
#   verdict-request <rev>  The request text for the auditor and the reviewer, then the accept command.
# --dry-run prints each command that writes and runs only the read-only checks.
#
# A monitor of side greps only for the last log line. It is exactly one of
#   SIDE DONE | SIDE FAIL rc=<N>
# (a timeout is "FAIL rc=124"). A killed unit prints nothing, so also stop when the unit is gone:
#   until grep -qE '^SIDE (DONE|FAIL)' LOG || ! systemctl --user is-active -q UNIT; do sleep 30; done
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
sha() { sha256sum < "$1" | cut -c1-64; }

# load_state: exports the saved state once; st <jq filter> reads it.
load_state() { STATE=$(mktemp /tmp/candidate-state.XXXXXX); trap 'rm -f "$STATE"' EXIT; node scripts/state.mjs export > "$STATE"; }
st() { jq -r "$1" "$STATE"; }

# scope: sets POS and NEG, the include and exclude globs of the next revision's allowedChangedFiles
# ("!" entries exclude). A new goport batch (--new-batch, or any revision after an accepted batch)
# gets open_revision.py's list; an open batch keeps its own.
scope() {
  local p
  local -a all
  if [[ -n $NEW_BATCH || $(st .batch.compilerAccepted) == true ]]; then
    mapfile -t all < <(python3 scripts/goport/open_revision.py --allowed)
  else
    mapfile -t all < <(st '.batch.allowedChangedFiles[]')
  fi
  POS=() NEG=()
  for p in "${all[@]}"; do if [[ $p == '!'* ]]; then NEG+=("${p#!}"); else POS+=("$p"); fi; done
}
# in_scope <path> [globs...]: true when the path matches a glob. Globs match like fnmatch (* crosses /).
in_scope() {
  local path=$1 pat
  shift
  # shellcheck disable=SC2053 # the patterns are globs
  for pat in "$@"; do if [[ $path == $pat ]]; then return 0; fi; done
  return 1
}
# pathspecs: git pathspecs of POS minus NEG.
pathspecs() {
  local p
  for p in "${POS[@]}"; do printf '%s\n' ":(glob)$p"; done
  for p in "${NEG[@]}"; do printf '%s\n' ":(exclude,glob)$p"; done
}

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

# check_branch <branch>: problems of <branch> as the next source of the checkout, against its HEAD. Paths
# that an exclude glob names (the saved state, target/) are skipped: open does not apply them. Prints each
# problem and returns 1 when there is one.
check_branch() {
  local branch=$1 wt base sha status path n=0 nrs=0 skipped=0
  local -a problems=()
  wt=$ROOT/$(st .batch.checkout)
  base=$(git -C "$wt" rev-parse HEAD)
  sha=$(git rev-parse --verify --quiet "$branch^{commit}") || die "unknown branch or commit: $branch"
  scope
  say "check $branch ${sha:0:9} against $(st .batch.checkout) ${base:0:9}; scope: ${POS[*]}${NEG[*]:+ except ${NEG[*]}}"
  while IFS= read -r -d '' status && IFS= read -r -d '' path; do
    if in_scope "$path" "${NEG[@]}"; then skipped=$((skipped + 1)); continue; fi
    n=$((n + 1))
    in_scope "$path" "${POS[@]}" || problems+=("outside allowedChangedFiles: $path")
    if [[ $status != D && $path == *.rs ]]; then
      nrs=$((nrs + 1))
      fmt_clean "$sha:$path" || problems+=("rustfmt --edition 2024 would change $path")
    fi
  done < <(git diff --no-renames --name-status -z "$base" "$sha")
  ((skipped == 0)) || echo "   $skipped changed path(s) under the excluded globs are not applied"
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
  local rev=$1 branch=$2 last wt base sha patch msg commit fp dirty
  local -a specs orv
  [[ -n $HYP && -n $CHANGE ]] || die "open needs --hypothesis and --change"
  [[ -z $NEW_BATCH || -n $ORIGIN ]] || die "--new-batch needs --origin"
  last=$(st '.batch.recoveryHistory[-1].revision')
  ((rev == last + 1)) || die "R$rev is not the next revision (R$((last + 1)))"
  [[ -n $NEW_BATCH || $(st .batch.compilerAccepted) != true ]] || die "batch $(st .batch.id) is accepted; pass --new-batch ID --origin TEXT"
  wt=$ROOT/$(st .batch.checkout)
  dirty=$(git -C "$wt" status --porcelain | grep -v '^?? crates/ts_goport/CANDIDATE.md$' || true)
  [[ -z $dirty ]] || die "$wt has changes besides CANDIDATE.md:"$'\n'"$dirty"
  check_branch "$branch" || die "check failed; nothing was changed"

  sha=$(git rev-parse "$branch^{commit}") base=$(git -C "$wt" rev-parse HEAD)
  mapfile -t specs < <(pathspecs)
  if git diff --quiet "$base" "$sha" -- "${specs[@]}"; then
    say "$(st .batch.checkout) already equals $branch in scope; no commit"
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
  else
    git -C "$wt" diff --quiet "$sha" HEAD -- "${specs[@]}" || die "$wt differs from $branch in scope"
    commit=$(git -C "$wt" rev-parse --short=9 HEAD)
    fp=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
  fi
  say "R$rev commit $commit, source fingerprint $fp"

  orv=(python3 scripts/goport/open_revision.py --revision "$rev" --fingerprint "$fp" --commit "$commit"
    --hypothesis "$HYP" --change "$CHANGE")
  [[ -z $NEW_BATCH ]] || orv+=(--new-batch "$NEW_BATCH" --origin "$ORIGIN")
  if [[ $fp != '<'* ]]; then
    say "open_revision.py checks (--dry-run, no write)"
    if [[ $DRY == 1 ]]; then "${orv[@]}" --dry-run; else "${orv[@]}" --dry-run > /dev/null; fi
  fi
  run "${orv[@]}"
  say "then: $SELF side $rev; after SIDE DONE: $SELF verdict-request $rev"
  say "commit the state: git add docs && git commit"
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
    bash -c "exec bash $SELF _side-unit $label $wt ${pin:--} $HOST ${NAME_MAP:--} >> $log 2>&1"
  if [[ $DRY == 1 ]]; then say "the unit runs:"; side_unit "$label" "$wt" "${pin:--}" "$HOST" "${NAME_MAP:--}"; fi
  echo "monitor: until grep -qE '^SIDE (DONE|FAIL)' $log || ! systemctl --user is-active -q $unit; do sleep 30; done; tail -8 $log"
}

# free_name <dir> <name>: <name>, or <name>-2, -3, ... when <dir>/<name> exists (gate labels are never reused).
free_name() { local n=$2 i=2; while [[ -e $1/$n ]]; do n=$2-$i i=$((i + 1)); done; echo "$n"; }

# side_unit <label> <checkout> <pin|-> <host|local> <name map|->: body of the side unit. Each finished step
# is a file in the cache dir (bins/, testbin/, tests-run/, tests.json, bound.json, gate.json,
# gate-compare.json, lsp.json, quality.json) and is reused. A failed compare writes tests-fail.json or
# gate-compare-fail.json instead; the gate record then moves to gate-fail.json, so the next run runs the
# gate again (move it back to gate.json to compare the same gate again). The other steps still run, so the
# verdict request has all the evidence. Last log line: SIDE DONE or SIDE FAIL rc=<N>.
side_unit() {
  local label=$1 wt=$2 pin=${3#-} host=$4 map=${5#-} key C B commit fp n r gl ll rc oracle lock synced=0 g l fails='' base
  local bt bts bg bgs
  local -a pinexec=()
  [[ $DRY == 1 ]] || trap 'rc=$?; if ((rc)); then echo "SIDE FAIL rc=$rc"; else echo "SIDE DONE"; fi' EXIT
  [[ -z $pin ]] || pinexec=(env GOPORT_PIN="$pin" python3 "$ROOT/scripts/upstream/pin.py" exec --)
  key=$(evidence_key "$wt" "$pin") C=$EVIDENCE/$key B=$EVIDENCE/$key/bins
  commit=$(git -C "$wt" rev-parse HEAD) lock=/tmp/goport-remote-${host%-lan}.lock
  say "$(date -u +%FT%TZ) side $label: $wt ${commit:0:9}, crates tree $(git -C "$wt" rev-parse HEAD:crates | cut -c1-12), pin ${pin:-current}, evidence $C"
  # The base: the last accepted revision's goport test results and gate manifest, pinned by sha256.
  if base=$(python3 scripts/goport/open_revision.py --base); then
    bt=$(jq -r .tests.path <<< "$base") bts=$(jq -r .tests.sha256 <<< "$base")
    bg=$(jq -r .gate.path <<< "$base") bgs=$(jq -r .gate.sha256 <<< "$base")
    [[ $(sha "$bt") == "$bts" && $(sha "$bg") == "$bgs" ]] || die "the base files differ from their sha256: $base"
    say "base $(jq -r '"\(.batch) R\(.revision)"' <<< "$base"): tests $bt, gate $bg"
  else
    need "no protected base (open_revision.py --base)"
    bt='<base results.json>' bg='<base gate manifest>'
  fi
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

  # goport tests: the test binaries of the checkout (build-goport-tests.sh takes the target lock itself),
  # every protected suite (goport-tests.sh, on zbook) and the per-name compare with the base results.
  # The run is cached in tests-run/; only a passing compare is cached, so a rerun with --name-map only
  # compares again.
  if [[ -f $C/tests.json ]]; then say "reuse goport tests $(jq -c .compare "$C/tests.json")"; else
    if [[ -f $C/testbin/bins.sha256 ]]; then say "reuse test bins $C/testbin (built from $(cat "$C/testbin/COMMIT"))"; else
      say "$(date -u +%FT%TZ) build test bins"
      run_sh "scripts/goport/build-goport-tests.sh $wt $C/testbin > $C/testbin-build.log 2>&1" || die "test bin build failed (log $C/testbin-build.log)"
    fi
    if [[ -f $C/tests-run/results.json ]]; then say "reuse test run $C/tests-run"; else
      say "$(date -u +%FT%TZ) goport tests"
      rc=0
      run_sh "rm -rf $C/tests-run.new && mkdir $C/tests-run.new && scripts/goport/goport-tests.sh $C/testbin $C/tests-run.new ${pin:+--pin $pin} > $C/tests-run.log 2>&1" || rc=$?
      if [[ $DRY == 0 ]]; then
        [[ $rc == 0 && $(tail -n 1 "$C/tests-run.log") == DONE && -f $C/tests-run.new/results.json ]] ||
          die "goport tests rc $rc, last line '$(tail -n 1 "$C/tests-run.log")' (log $C/tests-run.log)"
      fi
      run mv "$C/tests-run.new" "$C/tests-run"
    fi
    say "$(date -u +%FT%TZ) compare goport tests with the base"
    rc=0
    run_sh "python3 scripts/goport/compare-tests.py $bt $C/tests-run/results.json ${map:+--name-map $map }--out $C/tests-compare.json" || rc=$?
    if [[ $DRY == 0 ]]; then
      g=$C/tests.json; ((rc == 0)) || { g=$C/tests-fail.json; fails+="${fails:+; }goport tests: compare-tests.py rc $rc ($C/tests-compare.json)"; }
      jq --arg r "$C/tests-run/results.json" --arg s "$(sha "$C/tests-run/results.json")" --arg b "$(realpath "$bt")" --arg bs "$bts" \
        --arg tb "$C/testbin" --arg c "$(cat "$C/testbin/COMMIT")" --arg o "$C/tests-compare.json" \
        '{results: $r, sha256: $s, base: $b, baseSha256: $bs, testbin: $tb, commit: $c, compareOutput: $o, verdict,
          compare: (.total | {lost: (.lost | length), absent: (.absent | length), unrun: (.unrun | length), retained, recovered,
                              newNames, removedByMap, newFailed}),
          nameMap: (if .nameMap then {path: .nameMap.path, sha256: .nameMap.sha256} else null end),
          incomplete: .new.incomplete}' "$C/tests-compare.json" > "$g"
      ((rc)) || rm -f "$C/tests-fail.json"
    fi
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

  # Gate (full). The record is kept whatever its verdict: gate-compare.py below judges it.
  if [[ -f $C/gate.json ]]; then say "reuse gate $(jq -r '"\(.label) \(.verdict)"' "$C/gate.json")"; else
    gl=$(free_name "$R/compat/gate" "$label-full") rc=0
    remote_sync
    say "$(date -u +%FT%TZ) gate $gl on $host"
    on_host "$pin" "bash scripts/goport/gate.sh $gl --full --bins $B --commit $commit" "$C/gate-$gl.log" || rc=$?
    [[ $host == local ]] || run_sh "scripts/goport/remote.sh fetch $host $R/compat/gate/$gl >> $C/sync.log 2>&1"
    if [[ $DRY == 0 ]]; then
      tail -n 3 "$C/gate-$gl.log"
      [[ -f $R/compat/gate/$gl/manifest.json ]] || die "gate $gl rc $rc and no manifest (log $C/gate-$gl.log)"
      jq --arg l "$gl" --arg m "$R/compat/gate/$gl/manifest.json" --arg s "$(sha "$R/compat/gate/$gl/manifest.json")" --arg h "$host" --argjson rc "$rc" \
        '{label: $l, manifest: $m, sha256: $s, host: $h, exit: $rc, verdict, commit, upstreamPin,
          counts: ([.results[].status] | group_by(.) | map({(.[0]): length}) | add),
          failing: [.results[] | select(.status == "FAIL") | {id, detail}]}' \
        "$R/compat/gate/$gl/manifest.json" > "$C/gate.json"
    fi
  fi

  # Gate compare: each item against the base gate manifest (a MATCH stays MATCH, no new FAIL, no removed id,
  # the open editor long-growth items within the noise rule).
  if [[ -f $C/gate-compare.json ]]; then say "reuse gate compare $(jq -c .counts "$C/gate-compare.json")"; else
    say "gate compare with the base"
    rc=0
    run_sh "python3 scripts/goport/gate-compare.py $bg \$(jq -r .manifest $C/gate.json) --out $C/gate-compare.json > /dev/null" || rc=$?
    if [[ $DRY == 0 ]] && ((rc == 0)); then rm -f "$C/gate-compare-fail.json"; fi
    if [[ $DRY == 0 ]] && ((rc)); then
      mv "$C/gate-compare.json" "$C/gate-compare-fail.json"
      mv "$C/gate.json" "$C/gate-fail.json"
      fails+="${fails:+; }gate compare rc $rc: $(jq -r '[.regressions[] | "\(.id) (\(.why))"] | .[:10] | join(", ")' "$C/gate-compare-fail.json")"
    fi
  fi

  # LSP oracle (the batteries of the R121 to R125 side scripts).
  if [[ -f $C/lsp.json ]]; then say "reuse LSP oracle $(jq -r .label "$C/lsp.json")"; else
    ll=$(free_name "$R/ls-oracle/battery/results" "lsp-$label") rc=0
    oracle=$(python3 scripts/upstream/pin.py path oracle ${pin:+"$pin"})
    remote_sync
    # The goldens of this oracle (golden/<oracle sha256 prefix>) are not in every host mirror (R131: cup2).
    [[ $host == local ]] || run_sh "scripts/goport/remote.sh push $host $R/ls-oracle/battery/golden/$(sha256sum "$oracle" | cut -c1-12) >> $C/sync.log 2>&1"
    say "$(date -u +%FT%TZ) LSP oracle $ll on $host"
    l="cd target/worktrees/goport-int7 && python3 scripts/goport/lsp_oracle.py check --out-root $R/ls-oracle/battery"
    l+=" --battery $LSP_BATTERIES --goport $B/tsgo --oracle $oracle --label $ll --jobs 12"
    on_host "" "$l" "$C/lsp-$ll.log" || rc=$?  # the oracle path carries the pin
    [[ $host == local ]] || run_sh "scripts/goport/remote.sh fetch $host $R/ls-oracle/battery/results/$ll >> $C/sync.log 2>&1"
    if [[ $DRY == 0 ]]; then
      ((rc == 0)) || die "LSP oracle $ll rc $rc (log $C/lsp-$ll.log)"
      python3 - "$R/ls-oracle/battery/results/$ll/summary.json" "$ll" "$host" > "$C/lsp.json" <<'PY'
import json, sys
b = json.load(open(sys.argv[1]))['batteries'].values()
count = lambda k: sum(x['classes'].get(k, 0) for x in b)
print(json.dumps({'label': sys.argv[2], 'host': sys.argv[3], 'summary': sys.argv[1].replace('.json', '.md'),
                  'requests': sum(x['requests'] for x in b), 'diff': count('diff'), 'goportError': count('goport_error'),
                  'crash': count('crash') + sum(x['crashExits'] for x in b), 'timeout': count('timeout')}))
PY
    fi
  fi

  # Quality on the checkout: rustfmt and clippy (R114 and R124 were refused for quality alone).
  # Fingerprint before and after.
  if [[ -f $C/quality.json ]]; then say "reuse quality $(jq -c . "$C/quality.json")"; else
    say "$(date -u +%FT%TZ) quality: rustfmt and clippy"
    if [[ $DRY == 0 ]]; then
      local fpa fpb fmt=0 cl=0 warn
      fpb=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
      (cd "$wt" && rustfmt --edition 2024 --check $(git ls-files 'crates/ts_goport/**/*.rs') > "$C/rustfmt.log" 2>&1) || fmt=$?
      # After split step 1 (R131), goport_util and goport_lsproto are workspace crates built from ts_goport files.
      local pkgs=(-p ts_goport) p
      for p in goport_util goport_lsproto; do grep -q "\"crates/ts_goport/parts/$p\"" "$wt/Cargo.toml" && pkgs+=(-p "$p"); done
      (cd "$wt" && TS_CARGO_LOCK_ID=candidate-side TS_CARGO_SEPARATE_TARGET=1 CARGO_TARGET_DIR=$R/runtime/cargo-r113-clippy \
        "$ROOT/scripts/run-cargo-capped.sh" clippy --locked "${pkgs[@]}" --all-targets > "$C/clippy.log" 2>&1) || cl=$?
      fpa=$(python3 scripts/goport/fp.py "$wt" | cut -d' ' -f1)
      warn=$(grep -E '^(warning|error)' -A4 "$C/clippy.log" | grep -c -- '--> crates/ts_goport' || true)
      jq -n --arg fp "$fpa" --argjson fmt "$fmt" --argjson cl "$cl" --argjson w "$warn" --argjson same "$([[ $fpa == "$fpb" ]] && echo true || echo false)" \
        '{sourceFingerprint: $fp, rustfmtExit: $fmt, clippyExit: $cl, tsGoportWarnings: $w, fingerprintUnchanged: $same}' > "$C/quality.json"
      [[ $fmt == 0 && $cl == 0 && $warn == 0 && $fpa == "$fpb" ]] || fails+="${fails:+; }quality: rustfmt $fmt, clippy $cl, warnings $warn"
    fi
  fi

  say "$(date -u +%FT%TZ) evidence $C"
  for g in tests tests-fail bound gate gate-fail gate-compare gate-compare-fail lsp quality; do
    if [[ -f $C/$g.json ]]; then echo "   $g: $(jq -c 'del(.manifests, .failing, .knownOpen, .newAllowEntries, .regressions, .newIds, .fixed, .base, .new)' "$C/$g.json")"; fi
  done
  [[ -z $fails ]] || die "$fails"
}

# cmd_verdict <rev>: prints the verdict request texts from the state and the evidence cache, then the
# accept command. Exits 1 after printing when evidence is missing or failed.
cmd_verdict() {
  local rev=$1 wt key
  [[ $(st .batch.recoveryRevision) == "$rev" ]] || die "the batch is at R$(st .batch.recoveryRevision), not R$rev"
  [[ $(st .batch.protectedSet) == goport ]] || die "batch $(st .batch.id) is not a goport batch (protectedSet goport)"
  wt=$ROOT/$(st .batch.checkout)
  key=$(evidence_key "$wt" "$(st '.batch.upstreamPin.to // empty')")
  python3 - "$STATE" "$rev" "$EVIDENCE/$key" <<'PY'
import json, os, shlex, subprocess, sys
ROOT = '/home/theo/Code/sandbox/ts-rust'
s, rev, cache = json.load(open(sys.argv[1])), int(sys.argv[2]), sys.argv[3]
b = s['batch']
row, rows = b['recoveryHistory'][-1], b['recoveryHistory'][:-1]
wt = os.path.join(ROOT, b['checkout'])
git = lambda *a: subprocess.check_output(['git', '-C', wt, *a], text=True).strip()
load = lambda k: json.load(open(f'{cache}/{k}.json')) if os.path.exists(f'{cache}/{k}.json') else None
rel = lambda p: p.replace(ROOT + '/', '')
missing, ev = [], []
base = b['protectedBase']
head_commit = git('rev-parse', 'HEAD')
other = lambda c: '' if head_commit.startswith(c[:9]) else f' (run on commit {c[:9]} with the same crates tree)'

tests, tfail = load('tests'), load('tests-fail')
t = tests or tfail
if t:
    c = t['compare']
    ev.append(f"goport tests{' FAILED' if tfail and not tests else ''}: results {rel(t['results'])} sha256 {t['sha256']} "
              f"(test bins {rel(t['testbin'])}{other(t['commit'])}) against base {base['batch']} R{base['revision']} "
              f"{base['tests']['path']} sha256 {base['tests']['sha256']}: retained {c['retained']:,}, recovered {c['recovered']}, "
              f"lost {c['lost']}, absent {c['absent']}, unrun {c['unrun']}, new names {c['newNames']} ({c['newFailed']} failed), "
              f"removed by map {c['removedByMap']}; name map {t['nameMap']['path'] + ' sha256 ' + t['nameMap']['sha256'] if t['nameMap'] else 'none'}; "
              f"incomplete suites: {', '.join(t['incomplete'] or []) or 'none'}. Per-name compare {rel(t['compareOutput'])}.")
    if not tests:
        total = json.load(open(t['compareOutput']))['total']
        ev.append('goport test losses: ' + '; '.join(f'{k} {x}' for k in ('lost', 'absent', 'unrun') for x in total[k][:20]) + '.')
        missing.append('goport tests without a loss')
else:
    missing.append('goport tests (candidate.sh side)')
bound = load('bound')
if bound:
    ev.append(f"Bound runs {' and '.join(bound['rounds'])} ({', '.join(map(rel, bound['manifests']))}): all MATCH, the two runs identical; "
              f"bins {rel(cache)}/bins (bins.sha256 there, release profile).")
else:
    missing.append('bound runs (candidate.sh side)')
gate = load('gate') or load('gate-fail')
if gate:
    ev.append(f"Gate {gate['label']} ({gate['host']}{', pin ' + gate['upstreamPin'] if gate.get('upstreamPin') else ''}), manifest {rel(gate['manifest'])} "
              f"sha256 {gate['sha256']}: {gate['verdict']}, " + ', '.join(f'{gate["counts"][k]:,} {k}' for k in ('MATCH', 'ALLOWED', 'FAIL') if k in gate['counts'])
              + f"{other(gate['commit'])}." + (' FAIL items: ' + '; '.join(f"{f['id']}: {f['detail']}" for f in gate['failing']) + '.' if gate['failing'] else ''))
else:
    missing.append('gate (candidate.sh side)')
gc = load('gate-compare') or load('gate-compare-fail')
if gc:
    n = gc['counts']
    ev.append(f"Gate compare with base {base['batch']} R{base['revision']} {base['gate']['path']} ({gc['base']['label']}): "
              f"{n['regressions']} regressions, {n['knownOpen']} open-defect items within noise, {n['fixed']} fixed; "
              f"pin changed {gc['pinChanged']}, allow list changed {gc['allowListChanged']}, new allow entries {len(gc['newAllowEntries'])}. "
              f"Noise rule: {gc['noiseRule']}." + (' Open-defect items: ' + '; '.join(f"{k['id']} growth {k['growth']:.2f} (base {k['baseGrowth']:.2f})" for k in gc['knownOpen']) + '.' if gc['knownOpen'] else ''))
    if gc['regressions']:
        ev.append('Gate regressions: ' + '; '.join(f"{r['id']} {r['base']} -> {r['new']} ({r['why']})" for r in gc['regressions'][:20]) + '.')
        missing.append('gate compare without a regression')
else:
    missing.append('gate compare (candidate.sh side)')
lsp = load('lsp')
if lsp:
    ev.append(f"LSP oracle {lsp['label']} ({rel(lsp['summary'])}): {lsp['requests']:,} requests, {lsp['diff']} diff, {lsp['goportError']} goport_error, "
              f"{lsp['crash']} crash, {lsp['timeout']} timeout.")
else:
    missing.append('LSP oracle (candidate.sh side)')
quality = load('quality')
if quality:
    ev.append(f"Quality on the source: rustfmt exit {quality['rustfmtExit']}, clippy exit {quality['clippyExit']}, "
              f"{quality['tsGoportWarnings']} ts_goport warnings, fingerprint unchanged {quality['fingerprintUnchanged']}.")
else:
    missing.append('quality: rustfmt and clippy (candidate.sh side)')
pin = (b.get('upstreamPin') or {}).get('to')
head = (f"Batch {b['id']} (protected set goport), revision {rev}, source fingerprint {b['sourceFingerprint']} "
        f"({b['checkout']} commit {b['commit']}, crates tree {git('rev-parse', 'HEAD:crates')[:12]})."
        + (f' Go pin {pin} (GOPORT_PIN for every Go comparison).' if pin else ''))
evidence = '\n'.join(f'- {e}' for e in ev)
bind = f"naming the batch, the source fingerprint and the goport tests sha256 {t['sha256'] if t else '<missing>'}"
prev = next((r.get('commit') for r in reversed(rows) if r.get('commit')), None)
spec = ['--', '.', ':(exclude)docs/typechecker-state', ':(exclude)docs/typechecker-batches']
diff = git('diff', '--shortstat', prev, 'HEAD', *spec) if prev else 'unknown'
outside = git('diff', '--name-only', prev, 'HEAD', *spec, ':(exclude)crates/ts_goport').split() if prev else []
for role, key in (('audit_accepted_roster', 'auditor'), ('independent_reviewer', 'reviewer')):
    print(f"===== to {b[key]['agent']} ({role})")
    print(f'Root: verdict request for R{rev} (role {role}). {head}\n')
    if key == 'reviewer':
        print(f"Change: {(row.get('change') or '').rstrip('.')} (git diff {prev}..{b['commit']}:{diff}; outside crates/ts_goport: "
              f"{', '.join(outside[:30]) or 'none'}{' and more' if len(outside) > 30 else ''}).")
        print(f"Hypothesis: {row.get('hypothesis')}\n")
    print(f'Evidence:\n{evidence}')
    if key == 'reviewer':
        print('Please review the complete change against pinned Go (callers, caches, recursion, diagnostics, negative cases, '
              'repeat behavior), check that the protected set is complete (every base suite runs, every base name and gate item '
              f'is present or in a checked name map), check the evidence, and reply with VERDICT: PASS or STOP {bind}.\n')
    else:
        print('Please compare each base goport test name and each base gate item with the candidate, check the sources and hashes, '
              f'and reply with VERDICT: PASS or STOP {bind}.\n')
print('===== after two PASS verdicts')
print(f"python3 scripts/goport/accept_revision.py --revision {rev} --evidence {shlex.quote(cache)} --scope '<one line>' --outcome '<one line>'")
if missing:
    sys.exit('MISSING: ' + '; '.join(missing))
PY
}

DRY=0 HYP='' CHANGE='' MESSAGE='' NEW_BATCH='' ORIGIN='' CHECKOUT='' HOST=dbook-lan NAME_MAP=''
args=()
while (($#)); do
  case $1 in
    --dry-run) DRY=1; shift ;;
    --hypothesis) HYP=${2:?--hypothesis needs a value}; shift 2 ;;
    --change) CHANGE=${2:?--change needs a value}; shift 2 ;;
    --message) MESSAGE=${2:?--message needs a value}; shift 2 ;;
    --new-batch) NEW_BATCH=${2:?--new-batch needs a value}; shift 2 ;;
    --origin) ORIGIN=${2:?--origin needs a value}; shift 2 ;;
    --checkout) CHECKOUT=${2:?--checkout needs a value}; shift 2 ;;
    --name-map) NAME_MAP=$(realpath "${2:?--name-map needs a value}"); [[ -f $NAME_MAP ]] || die "no name map $2"; shift 2 ;;
    --gate-host) HOST=${2:?--gate-host needs a value}; [[ $HOST != auto ]] || die "--gate-host auto is not supported (sync-pin and fetch need one host); pick a free one with remote.sh status"; shift 2 ;;
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
  side:1) load_state; cmd_side "$1" ;;
  verdict-request:1) load_state; cmd_verdict "$1" ;;
  _side-unit:5) side_unit "$@"; exit 0 ;;
  *) usage ;;
esac
