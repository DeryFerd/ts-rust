# Typechecker wave 131

- Status: verified checkpoint, full port goal active
- Date: 2026-08-27 UTC
- Main branch: `july-ultra`
- Previous verified checkpoint: `400b2072`
- Runtime checkpoint: `74fd417a`
- Test-only lint follow-up: `4705d079`
- Input script groups: `d44d1c49`, `fa4f90de`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

The fixed reports retain every previous exact result. Full upstream semantic
parity and modern-project parity remain incomplete.

## Verified results

All 6,239 workspace tests passed at `74fd417a`, with zero failures and zero
ignored tests. This includes the pinned upstream parser tests. Formatting and
both generated AST checks passed.

Strict workspace Clippy passed for all targets at `4705d079`. That follow-up
changes one test's JavaScript selection from a suffix check to its exact input
name. Both inputs and all assertions remain unchanged. The affected test and
formatting checks passed. No production Rust behavior changed.

The semantic smoke report compares diagnostics, `.types`, and `.symbols`:

| Outcome | Variants |
| --- | ---: |
| Executed | 95 |
| Exact | 48 |
| Unsupported | 46 |
| Artifact mismatch | 1 |
| Fatal invariant | 0 |

One upstream skip remains. `jsDocTypedefTagNamespace` became exact through the
callback alias repair. No previous exact result was lost. The remaining
artifact mismatch is `functionExpandoPropertyDeclaration`.

The diagnostic-only milestone retains all 397 exact results in 511 executed
variants. Its other 114 results remain unsupported. There are no status
changes, exact losses, supported diagnostic mismatches, or fatal invariants.
Diagnostic equality alone is not semantic parity.

Both final reports identify clean `74fd417a`. Their manifests and variant keys
are unchanged. The callback-only reports at clean `dff2502f` have the same
results. Later input-script changes do not change the Rust checker or runner.

## Integrated changes

- JSDoc callback aliases retain their declared names and canonical identities.
- `noLib` suppresses library-reference loading and library observations.
- Canonical source traversal follows dependency order without changing stored
  source order or file IDs. Invalid scope edges do not enter that order.
- Module targets retain the actual import or require request mode. Canonical
  lookups no longer collapse different targets under one specifier.
- Config observations retain the actual parser inputs, probes, failures, and
  extends operations. Diagnostic rereads remain separate.
- Resolver results retain original paths and effective default modes.
- Project error artifacts retain exact text where the required source and
  diagnostic evidence exists. Unproven child-message boundaries remain
  unavailable. Library summary masking preserves the reviewed byte rules.

Each provider and the combined project changes received independent reviews.
The project composition also passed 574 focused compiler and fixture tests.

## Project inputs

Approved preparation scripts, focused safety tests, and input records are now
included for Hono, Svelte, ts-pattern, Effect, React Hook Form, Zod, and Query.
The integrated files retain their approved bytes, modes, and pins.

The seven groups passed 195 distinct offline checks. One optional Zod download
test was skipped. JavaScript and Python syntax checks passed. Root also reran
all 24 shared input-path guards after merging the initial six groups.

No real dependency install, project build, input rewrite, or cache rewrite ran
as part of this integration. Input preparation approval does not establish
compiler parity. See `project-inputs/integration-wave131.md` for source commit
chains and exact validation records.

## Evidence

These paths are under the main workspace's `target` directory:

- `wave131-combined-workspace.log`
- `wave131-combined-semantic-smoke.json`
- `wave131-combined-milestone.json`
- `wave131-combined-format.log`
- `wave131-combined-ast-kind.log`
- `wave131-combined-ast.log`
- `wave131-primary-clippy.log`
- `wave131-primary-source-order-test.log`
- `wave131-primary-format.log`
- `wave131-input-guards.log`

`wave131-combined-clippy.log` records the initial test-only lint failure, not
the final successful Clippy run. The two fixed report commands still exit
nonzero because their unsupported and mismatched variants remain explicit.

## Separate work

Iterator source integration, constructor composition, loop effects, expando
replay, additional artifact queries, and broader generic support remain on
separate branches. Their partial tests are not part of this checkpoint's
support claim. The later contextual-arrow flag repair is also separate.

New package-input and source-package-scope observations have separate provider
reviews. They are not part of this checkpoint. Package identity, source
realpaths, fresh diagnostic production, and other project evidence gaps remain
explicit where unavailable.

Go probes traced Hono's 91 changed type lines to cache-dependent rendering,
even without a source reset. The separate 221 pointer failures remain. The
original oracle reports, strict gates, and project inputs are unchanged.
Neither those probes nor the new object-creation witnesses establish parity.

## Build rules

Use `scripts/run-cargo-capped.sh`, an absolute manifest path, the shared Cargo
lock, and a target directory exclusive to each physical worktree. Set
`TS_CARGO_MEMORY_LIMIT_KIB=16777216` and `RUST_MIN_STACK=16777216`.

Keep new worktrees and large scratch on the workspace disk. Do not change
Cargo's `TMPDIR`, modify pinned upstream inputs, or count unsupported cases as
passes. The full port goal remains active.
