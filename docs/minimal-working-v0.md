# Minimal working v0

This is the experimental, supported product slice. It is intentionally narrower
than the repository's legacy all-features prototype.

## Supported contract

- Explicit TS, TSX, JS, and JSX input files.
- `--noCheck` single-pass transpilation.
- `--target esnext` and preserved ECMAScript modules via `--module esnext`.
- Type erasure, including type-only imports and `satisfies` expressions.
- JSX preservation via `--jsx preserve`.
- Basic syntax diagnostics with exact Go-oracle codes, ranges, messages, order,
  and exit status.
- Exact Go-oracle emit for the declared five-file corpus.
- Execution of emitted JavaScript in Node.

The reproducible invocation is:

```sh
tsgo <files> --ignoreConfig --noCheck --target esnext --module esnext \
  --jsx preserve --allowJs --outDir <directory> --pretty false
```

## Explicit exclusions

The following are not part of v0 and must not be used to make parity or
performance claims:

- semantic type checking;
- declaration emit and declaration maps;
- source maps;
- targets older than ESNext and their downlevel transforms;
- CommonJS, AMD, UMD, and System transforms;
- project references, incremental compilation, watch mode, and LSP;
- JSX transformation modes other than `preserve`;
- malformed-syntax recovery fidelity beyond the declared diagnostic corpus.

The broad prototype currently has 61 known legacy-test failures outside this
contract: 6 compiler tests, 4 malformed-recovery parser tests, and 51 printer
tests. They are excluded rather than presented as v0 failures. The v0 gate runs
all tests in the other workspace packages plus focused compiler/parser/CLI
tests for this contract.

## Gates

Run:

```sh
./scripts/verify-minimal-v0.sh
```

The gate requires:

1. changed-file whitespace, CLI formatting, and generated AST checks;
2. zero failures in the declared v0 test denominator;
3. byte-for-byte emit and syntax-diagnostic parity against the pinned Go oracle;
4. successful Node execution;
5. a release benchmark of equivalent successful work, reporting median, p95,
   speedup, and peak RSS for both implementations.

Set `TS_GO_ORACLE` if the pinned oracle is not installed at
`/home/theo/.local/bin/tsgo-oracle`. Cargo work is serialized and constrained by
the repository's 1 GiB cgroup runner.
