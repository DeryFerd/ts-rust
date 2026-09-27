#!/usr/bin/env bash
# Re-records the Go-side evidence for an upstream pin into its pin-keyed dirs (drift.md section 7
# step 3). Old evidence is never replaced: every recorder skips an output that exists.
#
# usage: rerecord.sh <key> [host] [steps]
#   key    pin key in UPSTREAM.json (scripts/upstream/pin.py)
#   host   alvin (default), dbook-lan, cup2, or local (run the host steps on this machine)
#   steps  comma list; default all, in this order:
#     prep      zbook: corpus-full and the corpus-int3 1,500-case shard from the pin's test cases, the
#               typesyms dumper and the Go dumps of query, hono and effect (record.py corpus, typesyms)
#     sync      zbook: pin.py sync, remote.sh sync-scripts, and the LS and API trace dirs
#     projects  host: saved oracle outputs of the gate project checks (record.py projects)
#     f1        host: conformance sample oracle outputs (record.py f1)
#     sweep     host: oracle-sweep/, with the existing tools-port/sweep.sh and sweep-hono-runtime.sh
#     emit      host: the emit oracle cache, with the existing emit/compare-emit.sh
#     ls        host: LS goldens, with the existing lsp_oracle.py: record, then selfcheck --runs 2 twice
#     api       host: API goldens, with the existing api_oracle.py: record, then selfcheck --runs 2
#     fetch     zbook: copy the pin root and the new golden dirs back from the host
# Host steps run with nice 15 under GOPORT_PIN=<key>, so the existing recorders use the pin oracle and
# write into the pin's dirs (pin.py exec). They take no host lock. The goport side of sweep and emit
# runs /usr/bin/true: only the oracle side is wanted. LS and API goldens go to
# <root>/golden/<pin oracle sha12>/, next to the old ones.
# For the current pin, only prep, sync, projects, f1 and fetch run: they write a fresh copy under the
# pin root that can be compared with the default caches. Logs: <pin root>/rerecord/<step>.log.
set -uo pipefail
REPO=/home/theo/Code/sandbox/ts-rust
R=$REPO/target/continuation-r97-goport
PIN=$REPO/scripts/upstream/pin.py
[[ $# -ge 1 && $1 != -* ]] || { sed -n '2,26p' "$0"; exit 2; }
KEY=$(GOPORT_PIN=$1 python3 "$PIN" show | python3 -c 'import json,sys; print(json.load(sys.stdin)["key"])') || exit 2
HOST=${2:-alvin}
STEPS=${3:-prep,sync,projects,f1,sweep,emit,ls,api,fetch}
CURRENT=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["current"])' "$REPO/UPSTREAM.json")
ROOT=$(python3 "$PIN" path root "$KEY")
ORACLE=$(python3 "$PIN" path oracle "$KEY")
# Oracle sha12 of a pin, from UPSTREAM.json. (Inside a pin run the default oracle path shows the pin oracle.)
osha() { python3 "$PIN" show "$1" | python3 -c 'import json,sys; print(json.load(sys.stdin)["oracle"]["sha256"][:12])'; }
OSHA=$(osha "$KEY")
JOBS=${JOBS:-12}
LOG=$ROOT/rerecord
LS_ROOTS=(ls-oracle/battery tests2/lsp complete/lsp)
TRACES=(ls-oracle/battery/traces ls-oracle/fourslash tests2/lsp/traces complete/lsp/traces tests2/api/traces tests2/api/tools)
cd "$REPO" || exit 2
mkdir -p "$LOG"

# Batteries with a selfchecked golden set for the current pin oracle (b3-effect was never finished).
batteries() {
  local d; for d in "$R/$1/golden/$(osha "$CURRENT")"/*/; do
    [[ -f $d/selfcheck-summary.json ]] && basename "$d"
  done
}

step_prep() {
  python3 scripts/upstream/record.py corpus "$KEY" && python3 scripts/upstream/record.py typesyms "$KEY"
}
step_sync() {
  python3 "$PIN" sync "$HOST" "$KEY" && bash scripts/goport/remote.sh sync-scripts "$HOST" || return
  local d; for d in "${TRACES[@]}"; do
    rsync -a --mkpath --ignore-existing "$R/$d/" "$HOST:$R/$d/" || return
  done
}
step_projects() { python3 scripts/upstream/record.py projects "$KEY" --jobs "$JOBS"; }
step_f1() { python3 scripts/upstream/record.py f1 "$KEY" --jobs "$JOBS"; }
step_sweep() {
  mkdir -p /tmp/port
  GOPORT_BIN=/usr/bin/true bash "$R/tools-port/sweep.sh" "../pins/$KEY/rerecord/sweep-runs" &&
    GOPORT_BIN=/usr/bin/true bash "$R/tools-port/sweep-hono-runtime.sh" "../pins/$KEY/rerecord/hono-rt-runs"
}
step_emit() { JOBS=4 bash "$R/emit/compare-emit.sh" /usr/bin/true "rerecord-$KEY"; true; }
step_ls() {
  local py=(python3 "$REPO/target/worktrees/goport-ls/scripts/goport/lsp_oracle.py") root b list extra
  for root in "${LS_ROOTS[@]}"; do
    list=$(batteries "$root" | paste -sd,); [[ -n $list ]] || continue
    extra=(); [[ $root == ls-oracle/battery ]] && extra=(--traces-dir "$R/ls-oracle")
    for b in ${list//,/ }; do
      # fourslash traces live in ls-oracle/fourslash; the other ls-oracle parts in ls-oracle/battery/traces.
      local tr=(); [[ $b == fourslash ]] && tr=("${extra[@]}")
      "${py[@]}" record --out-root "$R/$root" --battery "$b" --jobs "$JOBS" --oracle "$ORACLE" --request-timeout 300 "${tr[@]}" || echo "record $root $b exit $?"
      for run in 1 2; do
        "${py[@]}" selfcheck --out-root "$R/$root" --battery "$b" --jobs "$JOBS" --runs 2 --oracle "$ORACLE" "${tr[@]}" || echo "selfcheck $root $b run $run exit $?"
      done
    done
  done
}
step_api() {
  local py=(python3 "$R/tests2/api/tools/api_oracle.py") b
  for b in $(batteries tests2/api); do
    "${py[@]}" record --battery "$b" --jobs "$JOBS" --oracle "$ORACLE" || echo "record $b exit $?"
    "${py[@]}" selfcheck --battery "$b" --jobs "$JOBS" --runs 2 --oracle "$ORACLE" || echo "selfcheck $b exit $?"
  done
}
step_fetch() {
  bash scripts/goport/remote.sh fetch "$HOST" "$ROOT" || return
  local root
  [[ $KEY == "$CURRENT" ]] || for root in "${LS_ROOTS[@]}" tests2/api; do
    bash scripts/goport/remote.sh fetch "$HOST" "$R/$root/golden/$OSHA" || echo "no $root/golden/$OSHA on $HOST"
  done
}

run_step() {
  local s=$1 t=$(date +%s)
  echo "== $s $(date +%T)"
  "step_$s" > "$LOG/$s.log" 2>&1
  local rc=$?
  echo "   $s rc=$rc $(( $(date +%s) - t ))s: $(tail -n 1 "$LOG/$s.log" | cut -c1-150)"
  return $rc
}

HOST_STEPS=" projects f1 sweep emit ls api "
if [[ $KEY == "$CURRENT" ]]; then
  for s in ${STEPS//,/ }; do
    [[ " prep sync projects f1 fetch " == *" $s "* ]] || { echo "step $s does not run for the current pin $KEY" >&2; exit 2; }
  done
fi
[[ -n $OSHA && -e $ORACLE ]] || { echo "missing pin oracle $ORACLE" >&2; exit 2; }
[[ $HOST == local && -z ${GOPORT_PIN_ACTIVE:-} ]] || echo "rerecord $KEY on $HOST: $STEPS (pin oracle $OSHA, root $ROOT)"
if [[ $HOST == local ]]; then
  # Host steps need the pin overlay; pin.py exec starts it once for the whole run.
  export GOPORT_PIN=$KEY
  [[ -n ${GOPORT_PIN_ACTIVE:-} ]] || exec python3 "$PIN" exec -- bash "$0" "$KEY" local "$STEPS"
  rc=0
  for s in ${STEPS//,/ }; do
    [[ $s == sync || $s == fetch ]] && continue
    run_step "$s" || rc=1
  done
  exit $rc
fi
rc=0; batch=()
flush() {
  [[ ${#batch[@]} -gt 0 ]] || return 0
  local list; list=$(IFS=,; echo "${batch[*]}"); batch=()
  GOPORT_PIN=$KEY bash scripts/goport/remote.sh run "$HOST" "JOBS=$JOBS nice -n 15 bash scripts/upstream/rerecord.sh $KEY local $list" || rc=1
}
for s in ${STEPS//,/ }; do
  if [[ $HOST_STEPS == *" $s "* ]]; then batch+=("$s"); else flush; run_step "$s" || rc=1; fi
done
flush
exit $rc
