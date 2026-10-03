# npm packages

Local npm packages for the port, in the layout of the Go packages at the pin. Nothing here publishes.

- `typescript`: Go's JS launcher (`bin/tsc`, `lib/tsc.js`, `lib/getExePath.js`) and JS API (`dist`).
- `@typescript/typescript-linux-x64`: `lib/tsc` (a noembed build) and the lib files next to it.
- `wasm` (`ts-rust-wasm`): the WebAssembly build for Node, Deno, Bun and browsers. See
  [wasm/README.md](wasm/README.md).

The port adds one file to Go's layout: `install.js`, the postinstall (`lib/install.js`). On POSIX it
replaces `bin/tsc` with a relative symlink to the platform package's `lib/tsc`. Then `tsc` runs
without Node, which saves about 20 ms on every run. A symlink keeps the real path of the binary
in the platform package, where it reads the lib files. When the swap cannot happen, `bin/tsc`
stays Go's JS launcher, which still works.

Files:

- `pack.mjs` writes the two package dirs. It follows the Go checkout's `Herebyfile.mjs`
  (`buildNativePreviewPackages`, release profile `typescript`).
- `install.js` is the postinstall.

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
