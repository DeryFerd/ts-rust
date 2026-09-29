# Bundled lib provenance

The 108 `lib*.d.ts` files here are exact copies of `internal/bundled/libs` in
typescript-go at `16c25522e1230b69b11210cfad066d779e6319ba` (2026-08-19, the
bump B pin). Go generates them from the TypeScript submodule at
`5848bc5157b22ff7f4e3369f4645a514a433b15f`.

This is the only lib dir. `src/frontend/bundled/embed.rs` embeds every file
here (`bundled_lib!`), `scripts/copy-libs.sh` copies them next to the binaries
for a noembed build, and `scripts/gen-lib-names.py` writes
`src/core/lib_names.rs` from them.

The upstream contents are licensed under Apache-2.0 and retain Microsoft's
copyright notice in every generated declaration file.

## At a pin bump

1. Replace the files with `internal/bundled/libs` of the new pin:
   `rm crates/ts_goport/libs/lib*.d.ts && cp <go>/internal/bundled/libs/lib*.d.ts crates/ts_goport/libs/`.
2. Update the pin above.
3. When a file is added or removed, change the `bundled/embed.rs` entries and
   the `LIB_NAMES` list in `bundled.rs`, then run `scripts/gen-lib-names.py`.
4. Regenerate the lib parse and bind snapshots (`lib_parse.bin`, then
   `lib_bind.bin`).
