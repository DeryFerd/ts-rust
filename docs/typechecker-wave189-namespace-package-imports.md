# Package namespace imports

Status: all four unchanged original configurations match their complete error
artifacts. There are no unsupported results, header-only matches, mismatches,
or fatal invariants. This verifies diagnostics, not declaration emit.

Original:
`testdata/tests/cases/conformance/node/nodeModulesDeclarationEmitWithPackageExportsNoOutDir.ts`.
All eight virtual files and all original directives remain unchanged.

| Module | Expected diagnostics | Actual diagnostics | Full artifact |
| --- | ---: | ---: | --- |
| node16 | 5 | 5 | Exact |
| node18 | 5 | 5 | Exact |
| node20 | 0 | 0 | Exact |
| nodenext | 0 | 0 | Exact |

The Node16 and Node18 diagnostics are TS1479. The original options retain
`target=es2022` and `declaration=true` in every configuration.

## Change

Cold exported namespace constants retain their actual producer binding,
module symbol, export list, and source-owned type identity. They do not
publish the producer's variable value before its source check. Deferred
members cannot act as an empty structural object.

Warm reads keep the retained recursive and CommonJS wrapper member evidence.
Namespace proofs are boxed. Warm proof lookup follows the retained source
member order, without a linear search for each property.

Canonical Program diagnostics report TS1479 for checked CommonJS imports of
ESM files in Node16 and Node18. They use the validated resolution manifest.
The source loader retains the package-format hint from its existing package
read. The diagnostic code does not reread the VFS or depend on a bounded trace.
The existing named-import limits remain unchanged.

## Validation

- 382 namespace tests passed.
- All 276 compiler unit tests passed.
- All three new Node import diagnostic tests passed, including warm replay.
- Clippy passed for both crates, including tests, with `-D warnings`.
- Formatting, source-hash verification, and `git diff --check` passed.

Final validation had no failed or ignored tests. Logs and source hashes are retained
under `target/namespace-package-imports/after/validation-1` in the worktree.
The exact original scorecard is in
`docs/typechecker-wave189-namespace-package-imports.json`.

## Provenance

Pinned Go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`, clean.
Tested Rust: `eb7b38df0fa89a31b2765eb50a53d2b0a8f85784`, clean.
The before run at `8142bff97efccf69bb83c4b51ffe4d3ba515fb77` had four
unsupported configurations. The intermediate namespace commit `c551457f`
removed those unsupported results but still lacked TS1479 diagnostics.

The original runner finished with exit 0. It used a 16 GiB memory cap,
an 8 MiB main stack, a 16 MiB Rust worker stack, and a 300-second timeout.
Cargo used the shared build lock, the isolated target, `--locked --offline`,
and unchanged `TMPDIR`. No build output or Cargo fingerprint was copied.

Original source SHA256:
`03d822d51d9a7fc5f52d3163f4c882e05a8ac02d37fe8ae2f65bb5636292784e`.
Both original error baselines retain SHA256:
`80755fba693f77ba71bf267de166438988e9e5d4d075797e75a34996664fe772`.
Tested binary SHA256:
`45383095aac937a5245187c1f0b855cd1dfeb3e78129ef00be143af1413560ad`.
Scorecard SHA256:
`942ad4913a00895d8c6126b06298642e606d1ee3741c3d5c898372ef4e153f8b`.
