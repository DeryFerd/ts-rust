# Upstream provenance

The port tracks [`microsoft/typescript-go`](https://github.com/microsoft/typescript-go).

- Commit: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Commit date: 2026-06-19
- Local exploration cache: `~/.explore/repos/microsoft__typescript-go`

Generated Rust inputs under `spec/` record their own source paths and must be
updated intentionally. Normal Cargo builds must not depend on a Go or Node
installation. Differential and baseline maintenance commands may use an
external upstream checkout and compiler oracle.

The development oracle used for differential checks is built from the pinned
checkout with Go 1.26.4:

```sh
CGO_ENABLED=0 go build -o ~/.local/bin/tsgo-oracle ./cmd/tsgo
./scripts/run-cargo-capped.sh run -p ts_compare -- \
  ~/.local/bin/tsgo-oracle target/debug/tsgo -- --version
```

The upstream TypeScript submodule must be initialized for the full compiler
corpus. `TS_GO_REPO=/path/to/typescript-go ./scripts/run-cargo-capped.sh test
-p ts_fixture --test upstream_cases` validates fixture parsing across the
available cases and keeps invalid-UTF-8 scanner cases visible as a known
source-text requirement.
