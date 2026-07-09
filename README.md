# ts-rust

`ts-rust` is an experimental attempt to port
[`microsoft/typescript-go`](https://github.com/microsoft/typescript-go) to
Rust. It is not currently a replacement for `tsgo` or `tsc`.

## The model experiment

This repository is also an experiment in how capable `gpt-5.6-sol` is at
understanding, validating, and completing a compiler-sized systems port through
Codex and its subagents.

There is an important provenance caveat: the archived Codex log labels 236 of
the original implementation turns as an earlier model, one later turn as
`gpt-5.5`, and only the brief July 8 resume as `gpt-5.6-sol`. The existing code
is therefore the starting artifact for the `gpt-5.6-sol` experiment, not
evidence that every existing line was produced by that model name.

## Current state

The honest description is **a broad, unfinished compiler prototype with one
small, credible working slice**. The audit below is based on the checked-in code
at `02a8bf4`, fresh local tests on July 9, 2026, and the Codex implementation
logs.

### What is verified

The deliberately narrow [minimal working v0](docs/minimal-working-v0.md) can
process explicit TS, TSX, JS, and JSX files using:

- `--noCheck`;
- `--target esnext`;
- preserved ECMAScript modules with `--module esnext`;
- TypeScript type erasure, including type-only imports and `satisfies`;
- preserved JSX with `--jsx preserve`.

For the declared test corpus, the Rust binary:

- produces byte-for-byte identical output to the pinned Go oracle for five
  files covering TS, TSX, JS, and JSX;
- matches the oracle's diagnostics and exit behavior for four small malformed
  inputs;
- produces JavaScript that executes successfully in Node;
- measures 2.251 ms median versus 27.992 ms for Go in the repository's 31-run
  five-file microbenchmark, or 12.44x faster, while using less peak RSS.

That performance result applies only to this dedicated no-check fast path. It
is not a general TypeScript compiler performance claim.

### What exists but is not complete

The workspace contains 29 Rust crates, four supporting tools, about 200,000
lines of Rust, and implementations spanning:

- scanning, generated syntax kinds, parsing, binding, and diagnostics;
- semantic types, control-flow analysis, and type checking;
- configuration, module resolution, project graphs, and default libraries;
- JavaScript and declaration emit, downlevel transforms, and source maps;
- incremental builds, project references, watch mode, JSON-RPC, and LSP;
- fixture parsing, baseline comparison, and source-generation tools.

Source code and passing smoke tests for these layers do not establish
`typescript-go` parity. The parser can consume 12,752 pinned upstream case
files without crashing, for example, but that does not prove identical ASTs,
diagnostics, or output.

### What is currently broken or unproven

Fresh local runs pass **1,239 of 1,307 tests** and fail 68:

| Area | Passing | Failing | Important gaps represented by the failures |
| --- | ---: | ---: | --- |
| Checker | 147 | 2 | Flow diagnostics and inference |
| Parser | 155 | 4 | Malformed-input recovery |
| Compiler | 114 | 11 | Declarations, libraries, source maps, and emit |
| Printer | 512 | 51 | Downlevel and module transforms, JSX, private fields, and trivia |

The remaining workspace packages pass their local tests, but many of those
tests are self-authored and narrower than the upstream compatibility suites.
Neither repository verification script is fully green at this commit. Even
`scripts/verify-minimal-v0.sh` stops on the two checker failures, although its
focused v0 oracle and runtime tests pass independently.

The following should therefore be treated as experimental and unsupported:

- general semantic type checking;
- declaration emit, declaration maps, and source maps;
- targets older than ESNext and their transforms;
- CommonJS, AMD, UMD, and System module transforms;
- JSX transformation modes other than `preserve`;
- project references, incremental builds, watch mode, and LSP;
- broad malformed-syntax recovery and full upstream diagnostic parity.

Full parity has not been demonstrated against the upstream baseline, types,
symbols, trace, source-map, fourslash, or API suites. The type-checking parity
goal ended paused with unfinished definite-assignment and compatibility work.

## How the project got here

The implementation logs show three distinct Codex goal runs:

| Goal run | Outcome | Goal-accounted tokens |
| --- | --- | ---: |
| Full Rust port, June 22–26 | Produced the broad prototype. A later audit found 70 failing tests and measured the broad compiler 2.6–3.4x slower than Go for equivalent work. Paused. | 207,170,354 |
| `minimal-working-v0`, June 26 | Narrowed the claim to the explicit five-file no-check contract and built its oracle, runtime, and benchmark gates. Completed. | 1,439,471 |
| Type-checking parity, June 27–July 8 | Added substantial checker work, but never demonstrated full `tsgo` parity. Paused. | 7,438,681 |
| **Total** |  | **216,048,506 (~216 million)** |

The estimate uses Codex's goal-level `tokensUsed` counters for the three runs
that were explicitly tied to this repository. Those counters equal uncached
input plus output tokens. The raw session log records about 8.34 billion
input-plus-output tokens, but about 8.12 billion of those are cached context
replay, so that larger number is not a useful estimate of new inference spent
on the project. Work between goals and this README update are not included.

The history also explains why breadth is not the same as completion here. The
first goal landed hundreds of commits across many compiler subsystems before
the parity harness was authoritative. A recovery audit then reduced the scope
to one measurable path. The later checker goal expanded the scope again and
was suspended before cleanup and full verification were complete.

## Running the verified slice

The focused checks used for the current assessment are:

```sh
./scripts/run-cargo-capped.sh test -p ts_cli minimal_
./scripts/run-cargo-capped.sh test -p ts_compiler no_check_skips_semantic_diagnostics
./scripts/run-cargo-capped.sh build --release -p ts_cli --bin tsgo
RUNS=31 ./scripts/benchmark-minimal-v0.sh
```

The supported invocation is:

```sh
tsgo <files> --ignoreConfig --noCheck --target esnext --module esnext \
  --jsx preserve --allowJs --outDir <directory> --pretty false
```

The port is pinned to the upstream revision recorded in [UPSTREAM.md](UPSTREAM.md).
The broader completion criteria and missing upstream gates are described in
[docs/PORTING.md](docs/PORTING.md).
