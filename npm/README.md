# npm packages

Local npm packages for the port, in the layout of the Go packages at the pin, and the port's own
published set `tsc-rs` (see "tsc-rs releases" below).

- `typescript`: Go's JS launcher (`bin/tsc`, `lib/tsc.js`, `lib/getExePath.js`) and JS API (`dist`).
- `@typescript/typescript-linux-x64`: `lib/tsc` (a noembed build) and the lib files next to it.
- `wasm` (`ts-rust-wasm`): the WebAssembly build for Node, Deno, Bun and browsers. See
  [wasm/README.md](wasm/README.md).

The port adds one file to Go's layout: `install.js`, the postinstall (`lib/install.js`). On POSIX it
rewrites `bin/tsc` as a sh and JS polyglot. sh runs it as an exec of the platform package's
`lib/tsc` by a relative path, so `tsc` runs without Node, which saves about 20 ms on every run.
Node (`node node_modules/typescript/bin/tsc`) runs it as Go's JS launcher. The exec keeps the real
path of the binary in the platform package, where it reads the lib files. When the rewrite cannot
happen, `bin/tsc` stays Go's JS launcher, which still works.

The relative path is fixed at install. pnpm keeps a postinstall's result in its store (the
side-effects cache) and gives it to a later install of the same package in another layout
(hoisted, isolated or the global virtual store), where the path can name no file. Then `bin/tsc`
runs Go's JS launcher with Node, as Go's package does, about 20 ms slower per run.

Files:

- `pack.mjs` writes the package dirs. It follows the Go checkout's `Herebyfile.mjs`
  (`buildNativePreviewPackages`, release profile `typescript`).
- `install.js` is the postinstall.
- `getExePath.js` and `tsc-rs-readme.md` replace Go's launcher lookup and README in `tsc-rs`.

Build, test and time (see the header of each script):

```sh
GOPORT_BUILD_VERSION=7.1.0-dev.goport.1 scripts/run-cargo-capped.sh build --release -p ts_goport --bin tsgo --features noembed
GOPORT_PIN=<pin> scripts/goport/npm-pack.sh <out>/rs target/release/tsgo
GOPORT_PIN=<pin> scripts/goport/npm-pack.sh --go 7.1.0-dev.goport.1 <out>/go
scripts/goport/npm-test.sh <out>/rs <out>/test-rs
scripts/goport/perf-npm.sh <label> <out>/test-rs/proj <out>/test-go/proj   # on a quiet host
```

A shipped build uses `RELEASE_VERSION=<v> crates/ts_goport/scripts/build-release.sh` (noembed,
PGO and BOLT) in place of the cargo line.

## Linux libc

The platform package has no `libc` field, as Go's has none, so npm installs it on glibc and musl
systems alike. Go's tsc is static and starts on both. The default release tsc needs glibc 2.28 or
later: on Alpine, or on a distro with an older glibc, it does not start, and the JS launcher fails
too. `RELEASE_LIBC=musl RELEASE_PIE=0` in front of the build-release.sh line builds a static tsc
that starts on any x86-64 Linux. It is 0.5 to 1.9% slower (see the build-release.sh header), so it
is not the default.

## tsc-rs releases

`tsc-rs` is the same set under the port's own names: the main package `tsc-rs` (bin `tsc-rs`, so it
does not clash with the `tsc` of a `typescript` install) and one platform package per platform,
`@tsc-rs/linux-x64` and `@tsc-rs/darwin-arm64`. Its `lib/getExePath.js` finds
`@tsc-rs/<platform>-<arch>`.

The npm version (`--package-version`) is the port's own. The tsc is not stamped with it: it reports
the TypeScript version of the source (`7.1.0-dev`), because the compiler matches `typesVersions`
against that version. A tsc that reported 0.1.0 picked the `<=5.6` typings of zod's dependencies
and lost 2 of Go's 21 zod errors. The main package records the tsc version as `tscVersion` for the
postinstall check.

1. Linux, on a host with BOLT (zbook): `RELEASE_FEATURES=noembed RELEASE_LIBC=musl RELEASE_PIE=0
   crates/ts_goport/scripts/build-release.sh <out>/linux-x64` (no `RELEASE_VERSION`). Static musl:
   it starts on any x86-64 Linux.
2. macOS: the workflow `tsc-rs darwin build` (`.github/workflows/tsc-rs-darwin.yml`) builds on a Mac
   and uploads the artifact `tsc-darwin-arm64`. jemalloc does not cross-build for macOS with zig.
   `gh run download <run> -n tsc-darwin-arm64 -D <out>/darwin-arm64`. Both tsc builds must come
   from the same source.
3. Pack and test:

   ```sh
   GOPORT_PIN=<pin> scripts/goport/npm-pack.sh --name tsc-rs --package-version <v> \
     --also darwin-arm64=<out>/darwin-arm64/tsgo <out>/pkg <out>/linux-x64/bin/tsgo
   scripts/goport/npm-test.sh --name tsc-rs <out>/pkg <out>/test
   ```

4. Publish the platform packages first, then the main package: `npm publish <tgz> --tag next` for
   each. Check `npx tsc-rs@next` on each platform, then
   `npm dist-tag add tsc-rs@<v> latest` (and the same for each platform package).
