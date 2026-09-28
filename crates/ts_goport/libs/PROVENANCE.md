# Bundled lib overrides

These 7 files are copies of `internal/bundled/libs` in typescript-go at
`16c25522e1230b69b11210cfad066d779e6319ba` (the bump B pin). Six came in with
tsgo#4477 (`e7efb4b21`, TypeScript submodule `c3bd12d888` to `4d4f005c8`, bump A).
tsgo#4891 (`325211d3c`, submodule `4d4f005c8` to `5848bc515`, bump B) changed
`lib.es2018.intl.d.ts` and `lib.es2020.intl.d.ts` (the `Intl.PluralRules` call
signature is gone).

| file | sha256 |
|---|---|
| `lib.es2015.collection.d.ts` | `f0b6b1d3624fb143656dd86a8dd3e1950b7e65f218319b47bde52f65d47e2e4b` |
| `lib.es2015.core.d.ts` | `770011bd32a52f929fc98fbf9976c1fa9d80b6445171c02b08627fdba9778933` |
| `lib.es2015.symbol.d.ts` | `83e3871cda2abd4421970fa923cca51a9ce8cdbece6f898285643ab030cb80f3` |
| `lib.es2017.string.d.ts` | `6aaeba1e4f228fda4e9175e34d96807e2c6dc984d0b37a772b3af9365a456681` |
| `lib.es2018.intl.d.ts` | `b477b19cafa67ab59a4818c40d821674e641bf11e6200d5567b28cabedbc953d` |
| `lib.es2020.intl.d.ts` | `7b4f295ddb7e8c73f608bf54aa5d76b604b4fc44340a2eaa1f34040e7261afd4` |
| `lib.es5.d.ts` | `6388847232654d7fcbed7fe89ea511a65ad1f5104b41e905c43f90910e1408b6` |

`crates/ts_bundled/libs` stays at the old pin, because the protected
`ts_compiler` crate uses it. ts_goport takes these 7 names from here and every
other lib from `crates/ts_bundled/libs` (`src/frontend/bundled.rs`,
`bundled_lib!(goport ...)`). With these overrides the lib set equals
`internal/bundled/libs` at the pin byte for byte.

When a later pin changes a lib, copy it here from that pin, update this table
and the `bundled.rs` entry, then run `scripts/gen-lib-names.py` and regenerate
the lib parse and bind snapshots.
