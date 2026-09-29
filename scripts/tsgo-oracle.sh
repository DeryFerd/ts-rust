#!/usr/bin/env bash
set -euo pipefail
# GOPORT_PIN=<key> runs this against that upstream pin (scripts/upstream/pin.py). Unset: no change.
[[ -z ${GOPORT_PIN:-} || -n ${GOPORT_PIN_ACTIVE:-} ]] || exec python3 /home/theo/Code/sandbox/ts-rust/scripts/upstream/pin.py exec -- bash "$0" "$@"

# Runs the pinned tsgo oracle on a project without writing into it. Always adds
# --noEmit and puts .tsbuildinfo outside the project. Fails if any file under
# the project directory changed during the run.
# Usage: scripts/tsgo-oracle.sh -p <tsconfig> [tsgo flags...]
# Env: TS_GO_ORACLE_BIN (default ~/.local/bin/tsgo-oracle),
#      TS_GO_ORACLE_BUILDINFO_DIR (default: a fresh temporary directory).

oracle="${TS_GO_ORACLE_BIN:-$HOME/.local/bin/tsgo-oracle}"
config=""
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  case "${args[i]}" in
    -p | --project) config="${args[i + 1]:-}" ;;
    --tsBuildInfoFile | --outDir | --outFile | --declarationDir | -b | --build)
      echo "tsgo-oracle.sh: ${args[i]} is not allowed. The wrapper controls outputs." >&2
      exit 2
      ;;
  esac
done
if [[ -z "$config" || ! -e "$config" ]]; then
  echo "Usage: $0 -p <tsconfig> [tsgo flags...]" >&2
  exit 2
fi

config_path="$(realpath -- "$config")"
# The protected tree is the prepared input root, or the config directory.
if [[ "$config_path" =~ ^(.*/project-inputs/[^/]+/source)/ ]]; then
  project_dir="${BASH_REMATCH[1]}"
else
  project_dir="$(dirname -- "$config_path")"
fi
project_dir="${TS_GO_ORACLE_PROJECT_DIR:-$project_dir}"
buildinfo_dir="${TS_GO_ORACLE_BUILDINFO_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/tsgo-oracle.XXXXXX")}"
mkdir -p -- "$buildinfo_dir"
buildinfo_dir="$(realpath -- "$buildinfo_dir")"
case "$buildinfo_dir/" in "$project_dir/"*)
  echo "Build info directory must be outside the project: $buildinfo_dir" >&2
  exit 2
  ;;
esac

marker="$buildinfo_dir/.start"
touch -- "$marker"
status=0
"$oracle" "$@" --noEmit --tsBuildInfoFile "$buildinfo_dir/$(basename -- "$config_path" .json).tsbuildinfo" || status=$?
changed="$(find "$project_dir" -newer "$marker" -not -type d -print -quit 2>/dev/null)"
if [[ -n "$changed" ]]; then
  echo "tsgo-oracle.sh: the run wrote into the project input: $changed" >&2
  exit 3
fi
exit "$status"
