#!/usr/bin/env bash
# Checks the retries of testbox.sh with no testbox: PATH shims for blacksmith, rsync and ssh fail N times, then
# succeed. usage: scripts/goport/tests/testbox-retry.sh (prints one line per check, exits 1 when one fails)
# shellcheck disable=SC2016 # the run commands expand $FAKE_DIR in the shim, not here
set -euo pipefail
testbox="$(cd "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)/testbox.sh"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/bin" "$tmp/home/.blacksmith/testboxes/tbx_fake" "$tmp/fake" "$tmp/push"
: > "$tmp/home/.blacksmith/testboxes/tbx_fake/id_ed25519"
: > "$tmp/home/testbox.env"
echo data > "$tmp/push/a.txt"

# The shim logs each call to $FAKE_DIR/<name>.calls. While $FAKE_DIR/<name>.plan has lines, a call takes the
# first one, "RC MESSAGE", prints MESSAGE on stderr and exits RC. After that, calls succeed, and blacksmith
# testbox run runs its command here with bash.
cat > "$tmp/bin/fake" <<'SHIM'
#!/usr/bin/env bash
name=${0##*/}
# The keepalive of push runs in the background: no plan, no log.
[[ $name == ssh && " $* " == *" touch .testbox-last-activity "* ]] && exit 0
echo "$*" >> "$FAKE_DIR/$name.calls"
plan=$FAKE_DIR/$name.plan
if [[ -s $plan ]]; then
  read -r rc msg < "$plan"
  sed -i 1d "$plan"
  printf '%s\n' "$msg" >&2
  exit "$rc"
fi
if [[ $name == blacksmith ]]; then
  case $2 in
    warmup) echo tbx_new1 ;;
    status) printf 'ID STATUS HOST\n%s ready fake.host\n' "$4" ;;
    run) exec bash -c "${*: -1}" ;;
    stop) echo "Testbox $4 stopped" ;;
    list) echo "tbx_fake ready" ;;
  esac
fi
SHIM
chmod +x "$tmp/bin/fake"
for n in blacksmith rsync ssh; do ln -s fake "$tmp/bin/$n"; done
export PATH="$tmp/bin:$PATH" HOME="$tmp/home" FAKE_DIR="$tmp/fake" TESTBOX_ID=tbx_fake
export TESTBOX_ID_FILE="$tmp/id" TESTBOX_RETRY_WAITS="0 0 0 0 0"

fails=0
# check NAME EXPECTED ACTUAL
check() {
  if [[ $2 == "$3" ]]; then echo "ok   $1"; else echo "FAIL $1: expected '$2', got '$3'"; fails=$((fails + 1)); fi
}
# plan NAME COUNT "RC MESSAGE": the next COUNT calls of NAME fail.
plan() { for ((i = 0; i < $2; i++)); do echo "$3" >> "$tmp/fake/$1.plan"; done; }
calls() { if [[ -f $tmp/fake/$1.calls ]]; then wc -l < "$tmp/fake/$1.calls"; else echo 0; fi; }
retries() { grep -c '^testbox.sh: .* failed (rc .*); try [0-9] of 6 in 0 s$' "$tmp/err" || true; }
# t ARGS...: testbox.sh ARGS... with the plans set before, its rc in $rc and its output in $tmp/out and $tmp/err.
# Then the plans that are left go away.
t() {
  rm -f "$tmp"/fake/*.calls "$tmp/fake/ran.log"
  rc=0
  "$testbox" "$@" > "$tmp/out" 2> "$tmp/err" || rc=$?
  rm -f "$tmp"/fake/*.plan
}

plan blacksmith 2 "1 Error: could not get testbox status: request timed out after 30s"
t status
check "status: request timeout, rc" 0 "$rc"
check "status: request timeout, calls" 3 "$(calls blacksmith)"
check "status: request timeout, retry lines" 2 "$(retries)"
check "status: output" "tbx_fake ready fake.host" "$(tail -1 "$tmp/out")"

plan blacksmith 1 "1 Error: unauthorized"
t status
check "status: not transient, rc" 1 "$rc"
check "status: not transient, calls" 1 "$(calls blacksmith)"
check "status: not transient, error shown" "Error: unauthorized" "$(cat "$tmp/err")"

plan blacksmith 1 "1 Error: could not get testbox status: request failed: net/http: TLS handshake timeout"
t warmup
check "warmup: TLS timeout, rc" 0 "$rc"
check "warmup: TLS timeout, calls" 2 "$(calls blacksmith)"
check "warmup: TLS timeout, retry on stderr" 1 "$(retries)"
check "warmup: saved ID" tbx_new1 "$(cat "$tmp/id")"

plan blacksmith 1 'Error: request failed: Post "https://backend.blacksmith.sh/api/testbox/tbx_old9/warmup": EOF'
sed -i '$s/^/1 /;$s/EOF$/unexpected EOF/' "$tmp/fake/blacksmith.plan"
t warmup
check "warmup: error names a testbox, saved ID" tbx_new1 "$(cat "$tmp/id")"

plan rsync 2 "255 ssh: Could not resolve hostname fake.host: Name or service not known"
t push "$tmp/push"
check "push: DNS, rc" 0 "$rc"
check "push: DNS, rsync calls" 3 "$(calls rsync)"
check "push: DNS, retry lines" 2 "$(retries)"
check "push: output" "push $tmp/push" "$(cat "$tmp/out")"

plan rsync 1 "255 ssh: connect to host fake.host port 64000: Connection timed out"
t get some/dir/ "$tmp/got"
check "get: connect timeout, rc" 0 "$rc"
check "get: connect timeout, rsync calls" 2 "$(calls rsync)"

plan rsync 1 '23 rsync: [sender] link_stat "/x" failed: No such file or directory (2)'
t get /x "$tmp/got"
check "get: missing file, rc" 23 "$rc"
check "get: missing file, no retry" 1 "$(calls rsync)"

plan rsync 1 "255 runner@fake.host: Permission denied (publickey)."
t get /x "$tmp/got"
check "get: auth error, no retry" 1 "$(calls rsync)"

plan rsync 7 "255 ssh: Could not resolve hostname fake.host: Name or service not known"
t get /x "$tmp/got"
check "get: 6 tries, rc" 255 "$rc"
check "get: 6 tries, rsync calls" 6 "$(calls rsync)"
check "get: 6 tries, retry lines" 5 "$(retries)"

plan blacksmith 1 'Error: request failed: Post "https://backend.blacksmith.sh/api/testbox/tbx_fake/shutdown": net/http: TLS handshake timeout'
sed -i '$s/^/1 /' "$tmp/fake/blacksmith.plan"
t stop
check "stop: TLS timeout, rc" 0 "$rc"
check "stop: TLS timeout, calls" 2 "$(calls blacksmith)"

# run: the command line ran.log counts the starts of the command itself.
plan blacksmith 1 "1 Error: could not get testbox status: request timed out after 30s"
t run bash -c 'echo started >> "$FAKE_DIR/ran.log"; echo out; echo err >&2'
check "run: timeout before start, rc" 0 "$rc"
check "run: timeout before start, CLI calls" 2 "$(calls blacksmith)"
check "run: timeout before start, command starts" 1 "$(wc -l < "$tmp/fake/ran.log")"
check "run: stdout" out "$(cat "$tmp/out")"
check "run: stderr, no start marker" 0 "$(grep -c 'testbox.sh:start:' "$tmp/err" || true)"
check "run: stderr, command's line" err "$(tail -1 "$tmp/err")"

t run bash -c 'echo started >> "$FAKE_DIR/ran.log"; echo "Read from remote host fake.host: Connection reset by peer" >&2; exit 255'
check "run: drop after start, rc" 255 "$rc"
check "run: drop after start, no retry" 1 "$(calls blacksmith)"
check "run: drop after start, command starts" 1 "$(wc -l < "$tmp/fake/ran.log")"

t run bash -c 'echo started >> "$FAKE_DIR/ran.log"; echo "error: could not compile ts_goport" >&2; exit 101'
check "run: failed build, rc" 101 "$rc"
check "run: failed build, no retry" 1 "$(calls blacksmith)"

plan blacksmith 1 "1 Error: could not get testbox status: request timed out after 30s"
TESTBOX_RETRY_WAITS="" t status
check "TESTBOX_RETRY_WAITS empty: no retry" 1 "$(calls blacksmith)"

((fails == 0)) || { echo "$fails checks failed"; exit 1; }
echo "all checks passed"
