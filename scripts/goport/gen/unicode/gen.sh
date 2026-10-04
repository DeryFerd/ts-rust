#!/usr/bin/env bash
# Generate the Go Unicode data of crates/ts_goport/src/gostd from the Go that
# the pin N oracle uses: go1.27.1 (`unicode`, Unicode 17.0.0, and the
# `strconv` IsPrint tables) and golang.org/x/text v0.42.0 (`unicode/norm`,
# tables17.0.0.go).
#
#   gen.sh help    print this text
#   gen.sh         write gostd/unicode_tables.rs, gostd/strconv_isprint.rs and
#                  gostd/data/norm_*.bin of the checkout that holds this script
#
# Steps:
#   1. go1.27.1 runs main.go: writes unicode_tables.rs and a text dump, and
#      strconv_isprint.rs from src/strconv/isprint.go (checked against
#      strconv.IsPrint and strconv.IsGraphic for every rune).
#   2. rustc builds checkrs/main.rs with unicode_tables.rs as a module (no
#      cargo, no crate target dir) and prints the same dump. rustfmt formats
#      the file. The two dumps must be equal.
#   3. The norm package of x/text v0.42.0 (module cache, read-only) and its
#      transform dependency are copied into a work module with
#      norm/zz_dump_test.go. `go test -run TestDump` writes the norm tables
#      as little-endian binary files and norm_info.txt.
# Work files go to target/gen-unicode/ of the checkout.
set -euo pipefail

case "${1:-}" in
  help | -h | --help)
    sed -n '2,/^set -euo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  "") ;;
  *)
    echo "gen.sh: unknown argument $1 (see gen.sh help)" >&2
    exit 2
    ;;
esac

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../../.." && pwd)"
GOSTD="$REPO/crates/ts_goport/src/gostd"
WORK="$REPO/target/gen-unicode"
XTEXT="${GOMODCACHE:-$HOME/go/pkg/mod}/golang.org/x/text@v0.42.0"
GO="${GO:-go}"
mkdir -p "$WORK"

export GOTOOLCHAIN=local GOFLAGS= GO111MODULE=on GOPROXY=off GOWORK=off
"$GO" version | grep -q 'go1.27.1 ' || {
  echo "gen.sh: $GO is not go1.27.1 (set GO=<path to a go1.27.1 go>)" >&2
  exit 1
}
[ -d "$XTEXT/unicode/norm" ] || {
  echo "gen.sh: $XTEXT is missing (go mod download golang.org/x/text@v0.42.0)" >&2
  exit 1
}

# 1 and 2: unicode_tables.rs.
OUT="$GOSTD/unicode_tables.rs"
(cd "$HERE" && "$GO" run main.go -out "$OUT" -dump "$WORK/go-dump.txt" -isprint "$GOSTD/strconv_isprint.rs")
rustfmt --edition 2024 "$OUT" "$GOSTD/strconv_isprint.rs"
cat >"$WORK/checkrs_main.rs" <<RS
#[path = "$OUT"]
#[allow(dead_code)]
mod unicode_tables;
include!("$HERE/checkrs/main.rs");
RS
rustc --edition 2024 -O --crate-name checkrs -o "$WORK/checkrs" "$WORK/checkrs_main.rs"
"$WORK/checkrs" >"$WORK/rs-dump.txt"
if ! cmp -s "$WORK/go-dump.txt" "$WORK/rs-dump.txt"; then
  echo "gen.sh: Go and Rust dumps differ" >&2
  diff "$WORK/go-dump.txt" "$WORK/rs-dump.txt" | head -20 >&2
  exit 1
fi
echo "gen.sh: unicode OK, $(wc -l <"$WORK/go-dump.txt") dump lines equal; $(wc -l <"$OUT") lines in $OUT"

# 3: norm tables.
MOD="$WORK/xtext"
rm -rf "$WORK/xtext"
mkdir -p "$MOD/unicode/norm" "$MOD/transform" "$WORK/norm"
printf 'module golang.org/x/text\n\ngo 1.26.0\n' >"$MOD/go.mod"
for f in "$XTEXT"/unicode/norm/*.go; do
  case "$f" in *_test.go) continue ;; esac
  cp "$f" "$MOD/unicode/norm/"
done
for f in "$XTEXT"/transform/*.go; do
  case "$f" in *_test.go) continue ;; esac
  cp "$f" "$MOD/transform/"
done
cp "$HERE/norm/zz_dump_test.go" "$MOD/unicode/norm/"
chmod -R u+w "$MOD"
(cd "$MOD" && GEN_OUT="$WORK/norm" "$GO" test -count=1 -run '^TestDump$' ./unicode/norm)
cp "$WORK"/norm/norm_*.bin "$GOSTD/data/"
echo "gen.sh: norm OK"
cat "$WORK/norm/norm_info.txt"
