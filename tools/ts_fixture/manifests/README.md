# Fixed checker manifests

`checker-smoke-v1.json` freezes the 96-variant Wave 0 checker shard. It is a
reviewed selection, not a run-time sample: every entry names one complete
schema-5 `variantKey`, and a supported result never rotates out merely because
another case becomes easier.

## Smoke policy

The manifest contains twelve variants from each of the eight families in
`docs/typechecker-completion-goal.md`. Every family has six programs whose
upstream diagnostic baseline is clean and six whose upstream baseline contains
errors. The selection also retains single- and multi-file programs, declaration
files, TypeScript, TSX, JavaScript, Bundler/ESM, CommonJS, and NodeNext shapes.

`family` and `tags` are reviewed routing metadata, not a substitute for the
upstream oracle. `case`, `options`, `expectedBaseline`, `expectedDiagnostics`,
`fileShape`, and `sourceKinds` are redundant audit fields. A manifest consumer
must resolve the `variantKey` from discovery and reject the manifest if any
redundant field is absent or disagrees with the discovered variant.
`expectedBaseline` uses an explicit JSON `null` when no baseline exists.

## Digest

The manifest digest is XXH3-128 over the ordered variant keys. The canonical
byte stream is each UTF-8 `variantKey` followed by one LF byte, including the
last key. Metadata and formatting do not affect this identity; changing or
reordering a key does.

For a checked-out manifest, the digest can be audited with:

```sh
jq -r '.variants[].variantKey' checker-smoke-v1.json | xxh128sum
```

## Deterministic validation contract

Before the shard is used as a merge gate, the fixture runner must:

1. require the pinned upstream SHA and complete oracle-manifest digest;
2. discover the complete corpus/oracle exactly as for an ordinary scorecard;
3. require every unique named case to resolve exactly once to a runnable case,
   then fully expand those cases and resolve every manifest key exactly once;
4. reject duplicate, missing, extra, stale, or differently attributed keys;
5. validate the ordered-key digest, eight 12-key quotas, and six-clean/six-error
   split in every family from the upstream baseline rather than trusting the
   checked-in audit fields;
6. execute only those 96 variants in manifest order while retaining typed
   capability and fatal outcomes; and
7. write the manifest name and digest into scorecard provenance.

The runner implements this contract with:

```sh
TS_GO_REPO=/path/to/typescript-go \
  cargo run -p ts_fixture --bin ts_fixture_baseline -- \
  --diagnostics \
  --canonical-checker \
  --variant-manifest tools/ts_fixture/manifests/checker-smoke-v1.json \
  --scorecard-json checker-smoke-scorecard.json
```

Fixed-shard execution requires a clean upstream checkout at the manifest's
exact SHA. The runner still computes `provenance.manifestDigest` from the
complete oracle manifest; `provenance.fixedShard` separately records the fixed
selection's name, schema/key versions, digest, algorithm, and variant count.

Regeneration requires two identical discoveries at the pinned upstream epoch,
a fresh schema-5 scorecard, and review of every added, removed, or retagged key.

No explicit cross-file relative import/re-export cycle was identified in the
completed 500-case selection source. Add a deterministic cycle case to the
512-variant milestone manifest; changing the smoke shard for that reason
requires an explicit reviewed key replacement rather than dynamic sampling.
