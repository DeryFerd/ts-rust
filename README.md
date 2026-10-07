# ts-rust (aka tsc-rs)

I wanted to see if LLMs could port the TypeScript compiler, checker and lsp to Rust. Turns out they can.

It [cost over $420,000](#how-did-this-go) in tokens to do it, but you could probably have done it for ~$20k (see below)

## Motivations

- Test model capabilities
- Make a fast TypeScript type checker
- Make a ts checker that can work in WASM with high performance
- Memes

## Warnings

**This is an early release.** It is not yet a full replacement for `tsc` in every project. See
[Known problems](#known-problems).

Also worth mentioning: I've never read a line of this code.

## Install

Be warned, I have no idea if this will actually work.

```sh
npm install -D tsc-rs
npx tsc-rs -p tsconfig.json
```

## How did this go?

I used a lot of OpenAI models to try and complete this port. In total I did **over $400,000 in API priced tokens with GPT-5.6 Sol and GPT 6 Astra**. They wrote over 1.3m lines of Rust over multiple months of /goal loops and never got past like 84% compat.

When I saw how little my Claude Code limits were burning, I figured it'd be fun to throw Opus 5.5 at this. It had a working v0 in 10 hours.

I assumed it kept using the code the Codex models wrote. I was wrong. **Opus 5.5 started from scratch. It got further than Astra in 1/10th the time.**

I let it keep going, and it definitely did. Total token spend was **~$24,047 of API spend over 2 weeks**. I was using my Claude accounts, and it worked out to somewhere between **925% and 983% of my $200 plan weekly limits**.

Expensive, for sure, but not that bad considering how much work has went into typescript-go.

# "The Slop Line"

Everything below this was written by my LLMs, not me. 

## What actually is this?

ts-rust is a direct port of Microsoft's native TypeScript compiler, which is written in Go
([microsoft/TypeScript](https://github.com/microsoft/TypeScript), formerly
[typescript-go](https://github.com/microsoft/typescript-go)). It keeps Go's algorithms and
behavior and has the same command line (`tsc`), language server and API.

## Install

```sh
npm install -D tsc-rs
npx tsc-rs -p tsconfig.json
```

`tsc-rs` takes the same options as `tsc`. The npm package is `tsc-rs` so that it does not clash
with the `typescript` package. Each [release](https://github.com/pingdotgg/ts-rust/releases) also
has a standalone archive per platform: the `tsc` binary with the lib files next to it.

Platforms: Linux x64 (static, any distribution) and macOS arm64. Windows and Linux arm64 are not
available yet.

To use it in VS Code, see the [npm package README](npm/tsc-rs-readme.md#vs-code).

## Effect diagnostics

`tsc-rs` has the [Effect](https://effect.website) language service diagnostics built in (codes
377xxx), so an Effect project needs no second compiler. They come from the same check as the
TypeScript diagnostics, and the language server shows them too. They run only when the tsconfig has
the plugin, as with `@effect/language-service`:

```json
{ "compilerOptions": { "plugins": [{ "name": "@effect/language-service" }] } }
```

The rules, options and `@effect-diagnostics` comments are a port of
[Effect-TS/tsgo](https://github.com/Effect-TS/tsgo) 0.46.1. The editor features of the language
service (quick fixes, refactors, hover, completions) are not ported.

## Status

The port is pinned to one upstream revision ([UPSTREAM.md](UPSTREAM.md)) and compared with Go at
that revision:

- **Same results.** TanStack Query core and Hono check with diagnostics identical to Go's. All
  181,711 ported Go tests pass. The language server and API answers match Go on the oracle test
  sets.
- **Faster.** On 60 open-source projects, type checking takes about half of Go's time (geometric
  mean). The preview packages are built in CI without PGO and BOLT, so they are slower than that
  measured build.
- **Real projects.** On 120 open-source repos, the command-line output differs from Go's only in
  the problems below and where Go's own output changes from run to run.

## Known problems

- In some monorepos, the source files of a workspace package are reachable both through
  `node_modules` and through a direct import. There, `tsc-rs` can write output for more of those
  files than `tsc` does.
- In `tsc -b`, when one project imports the output of another project without a project reference,
  `tsc-rs` can report TS2307 (cannot find module) where `tsc` happens to build the other project
  first. Add the reference to fix it.
- `tsc -b --watch` can stop with an internal error (exit code 70) after some edits.
- In the editor, memory grows slowly during long edit sessions.
- `tsc-rs --version` prints the TypeScript version that it ports (7.1.0-dev), not the npm
  version. The compiler matches `typesVersions` against it.

## Development

`crates/ts_goport` is the compiler. It has two parts crates, `goport_util` and `goport_lsproto`,
in `crates/ts_goport/parts`, and uses the lib files in `crates/ts_goport/libs`.
`tools/ts_ast_codegen` generates `crates/ts_goport/src/astdata`, and
`tools/ts_diagnostics_codegen` generates `crates/ts_goport/src/diagnostics/catalog.rs` and
`crates/ts_goport/src/diag.rs`. `crates/ts_wasm` is the WebAssembly build
([npm/wasm](npm/wasm/README.md)).

```sh
./scripts/run-cargo-capped.sh build --release -p ts_goport --bins
./scripts/verify.sh
```

The bins are `goport` (type check) and `tsgo` (the Go `tsgo` command line). The Go baseline tests
run with
`TS_GO_REPO=/path/to/typescript-go ./scripts/run-cargo-capped.sh test -p ts_goport --test go_baselines`.

- Port rules: [crates/ts_goport/PORTING.md](crates/ts_goport/PORTING.md)
- Measurement and gate scripts: [scripts/goport](scripts/goport/README.md)
- npm packages and releases: [npm/README.md](npm/README.md)
- Typechecker work rules: [AGENTS.md](AGENTS.md), the
  [accountability rules](docs/typechecker-accountability.md) and the
  [saved state](docs/typechecker-state/current.json)
- How the project started: [docs/history.md](docs/history.md)

## Releases

Push a tag `v<version>` (for example `v0.1.0`). The
[release workflow](.github/workflows/release.yml) builds, packs and tests the packages, publishes
them to npm and creates a GitHub release. A stable version goes to the dist-tag `latest`, and a
prerelease version (`v0.2.0-beta.1`) to `next` and a GitHub prerelease. See
[npm/README.md](npm/README.md#tsc-rs-releases).

## License

[MIT](LICENSE). The port keeps the licenses and notices of the code it ports: TypeScript
(Apache-2.0) and parts of the Go standard library (BSD-3-Clause). See [NOTICE.md](NOTICE.md).
