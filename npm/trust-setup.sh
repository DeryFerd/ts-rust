#!/usr/bin/env bash
# One-time setup of npm trusted publishing for the tsc-rs packages. Run it by hand, logged in to
# npm as an owner of tsc-rs and the @tsc-rs org, with 2FA on (npm asks for a code once).
#
# For each package (tsc-rs, @tsc-rs/linux-x64, @tsc-rs/darwin-arm64) it:
#   1. publishes a 0.0.0-placeholder version when the package is not on npm yet: npm can only
#      trust a workflow for a package that exists. The release workflow refuses 0.0.x tags, so a
#      release never collides with a placeholder (tsc-rs has a 0.0.1 placeholder).
#   2. trusts .github/workflows/release.yml of pingdotgg/ts-rust in the environment `npm` to
#      publish it. When the package already trusts something else, it stops and prints the
#      revoke command (it does not revoke by itself).
# npm drops a new trust that publishes nothing in 2 days. So run this shortly before the first tag.
#
# usage: npm/trust-setup.sh          needs npm 11.15.0 or later (npm trust)
set -euo pipefail
[[ ${1:-} != help ]] || { sed -n '2,14p' "$0" >&2; exit 2; }
repo=pingdotgg/ts-rust
packages=(tsc-rs @tsc-rs/linux-x64 @tsc-rs/darwin-arm64)

npm_version=$(npm --version)
[[ $(printf '%s\n' 11.15.0 "$npm_version" | sort -V | head -1) == 11.15.0 ]] ||
  { echo "npm $npm_version: npm trust needs 11.15.0 or later (npm install -g npm@11)" >&2; exit 1; }
echo "npm user: $(npm whoami)"

for name in "${packages[@]}"; do
  if npm view "$name" version > /dev/null 2>&1; then
    echo "$name is on npm"
  else
    dir=$(mktemp -d)
    cat > "$dir/package.json" << EOF
{
  "name": "$name",
  "version": "0.0.0-placeholder",
  "description": "A Rust port of the TypeScript 7 compiler. Placeholder: not released yet.",
  "license": "MIT",
  "repository": { "type": "git", "url": "git+https://github.com/$repo.git" }
}
EOF
    (cd "$dir" && npm publish --access public --tag placeholder)
    rm -rf "$dir"
    echo "$name: placeholder 0.0.0-placeholder published"
  fi
done

for name in "${packages[@]}"; do
  # A configuration has an id (npm trust revoke --id). npm keeps one per package.
  trust=$(npm trust list "$name" --json 2> /dev/null || true)
  if ! grep -q '"id"' <<< "$trust"; then
    npm trust github "$name" --file release.yml --repo "$repo" --env npm --allow-publish --yes
    sleep 2
  elif ! { grep -q "$repo" <<< "$trust" && grep -q 'release\.yml' <<< "$trust" &&
    grep -q '"npm"' <<< "$trust"; }; then
    echo "$name trusts another repo, workflow or environment:" >&2
    npm trust list "$name" >&2
    echo "revoke it with: npm trust revoke $name --id <id>, then run this again" >&2
    exit 1
  fi
  npm trust list "$name"
done
