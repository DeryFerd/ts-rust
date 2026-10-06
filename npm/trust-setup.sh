#!/usr/bin/env bash
# One-time setup of npm trusted publishing for the tsc-rs packages. Run it by hand, logged in to
# npm as an owner of tsc-rs and the @tsc-rs org, with 2FA on (npm asks for a code once).
#
# For each package (tsc-rs, @tsc-rs/linux-x64, @tsc-rs/darwin-arm64) it:
#   1. publishes a 0.0.1 placeholder when the package is not on npm yet: npm can only trust a
#      workflow for a package that exists.
#   2. trusts .github/workflows/release.yml of pingdotgg/ts-rust in the environment `npm` to
#      publish it, unless the package has a trusted publisher already.
# npm drops a new trust that publishes nothing in 2 days. So run this shortly before the first tag.
#
# usage: npm/trust-setup.sh          needs npm 11.15.0 or later (npm trust)
set -euo pipefail
[[ ${1:-} != help ]] || { sed -n '2,12p' "$0" >&2; exit 2; }
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
  "version": "0.0.1",
  "description": "A Rust port of the TypeScript 7 compiler. Placeholder: not released yet.",
  "license": "MIT",
  "repository": { "type": "git", "url": "git+https://github.com/$repo.git" }
}
EOF
    (cd "$dir" && npm publish --access public)
    rm -rf "$dir"
    echo "$name: placeholder 0.0.1 published"
  fi
done

for name in "${packages[@]}"; do
  # A configuration has an id (npm trust revoke --id).
  if ! npm trust list "$name" --json 2> /dev/null | grep -q '"id"'; then
    npm trust github "$name" --file release.yml --repo "$repo" --env npm --allow-publish --yes
    sleep 2
  else
    echo "$name has a trusted publisher already:"
  fi
  npm trust list "$name"
done
