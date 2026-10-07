# Effect diagnostics reference data

`effectDiagnosticMessages.json` is copied unchanged from
[Effect-TS/tsgo](https://github.com/Effect-TS/tsgo) at the `@effect/tsgo@0.46.1`
release commit `f1a7cad0292d9d315e7f87694f127f605711d55e`
(`internal/diagnostics/effectDiagnosticMessages.json`).

`scripts/effect/gen-effect-messages.mjs` turns it into
`crates/ts_goport/src/diagnostics/effect_catalog.rs` (the messages) and
`crates/ts_goport/src/effect/diag.rs` (their Go names). Run it again after a
change to the JSON.
