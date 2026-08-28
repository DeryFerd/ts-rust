# Class admission controls

These Go controls retain the three constructor inputs from
`source_class_second_wave.rs` and the exact two-file compiler input from
`canonical_program_rejects_a_later_unsupported_file_without_fallback`.

The upstream checkout must be clean at
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. The runner requires Go 1.26.5 on
linux/amd64, uses the shared build queue and a 16 GiB scope, and builds offline.
It does not change the upstream checkout or TMPDIR.

```sh
bash tests/oracles/class-admission/run.sh GO UPSTREAM NEW_OUTPUT MODULE_CACHE
```

All arguments must be absolute paths. The module cache must already contain
the pinned dependencies. The output directory must not exist. The runner
records the Go version, input hashes, upstream commit, and Rust checkout state.
Each successful case prints a JSON record with its exact sources and options.

The direct Rust checker fixtures use loose checking and an ES5 target. They
bind no default library. Go uses `strict: false`, `target: es5`, and `noLib`
to reproduce that input set. The compiler fixture uses strict checking, ES5,
and the ES5 library. Both checks use script modules.

Source diagnostics run before explicit class queries. The controls then check
the named instance and constructor types, retain the same class symbol and
type pointers, and repeat the diagnostic reads. These are retained warm reads,
not a claim of fresh diagnostic production after resetting the Go checker.
