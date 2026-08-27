# Project graph limits

`Program::project_graph_snapshot` returns the loader's retained facts. It does
not certify that the graph or the canonical module manifest matches upstream.
Its `missing_evidence` field names inputs the loader does not retain.

## Mode-specific module targets

`Program::resolved_modules` keys targets by canonical containing path, module
specifier, and request mode. The canonical manifest uses the exact request mode
for each specifier node. An `.mts` source can retain different targets for these
imports:

```ts
import { value } from "pkg";
import other = require("pkg");
```

`canonical_module_resolution_modes.rs` checks this through public canonical
queries, value types, declaration owners, and replay in both source orders.
Declaration-only tests with `skipLibCheck` also check explicit `resolution-mode`
attributes, an unresolved target in only one mode, and shared ambient targets.
A JSX test checks that a successful require lookup cannot hide a missing
import-mode runtime.

Unresolved source `import = require` checking remains explicitly unsupported.
The test suite preserves that failure class. The legacy checker still projects
module targets to a map keyed only by specifier text. These bounded canonical
checks do not certify mixed-mode legacy checking, emit, or full resolution
parity. The graph snapshot remains a report of retained inputs and results.

## Missing input evidence

The config resolver retains an ordered prefix of its existing probes, reads,
extends decisions, and cycles. This adds no filesystem calls. The observation
limit is 16,384 events and 16 MiB of UTF-8 string data. Omitted events are counted.
`is_complete` describes retention only. It does not mean that the config was
valid, that resolution succeeded, or that the complete Program was observed.

Read events contain the VFS text passed to parsing, not raw disk bytes. The VFS
can remove a BOM or decode UTF-16. Report fields use `parserInputText`,
`parserInputTextUtf8ByteCount`, and `parserInputTextDigest`. Repeated reads stay
separate. The compiler still performs its later diagnostic read in the same
place. `ProgramGraphConfig::source_text` and the report's
`diagnosticSourceTextDigest` describe that later text, which can differ.

Resolved module records retain the lookup candidate before optional realpath
handling. Every resolution attempt retains the effective import or require
mode, including default-mode and failed attempts. Config parse and extends
gaps remain when observations are incomplete. A missing leaf text remains a
separate gap.

## Resolver package inputs

Each resolver worker retains an ordered prefix of its package JSON probes and
reads. The default limit is 256 events and 256 KiB of UTF-8 string data per
worker. Limits do not change resolution choices or cache keys. Repeated reads
stay separate, including changes to the text or read result.

`resolutions[].packageJsonInputs` contains those original worker inputs. Its
`inputOrigin` is `resolver_worker`. A cache hit shares the original inputs and
does not perform fresh reads. The report does not infer whether a request was a
cache hit. A synthetic result has `null` inputs. An observed worker with no
package accesses has an empty event list with complete retention. Missing or
incomplete inputs keep the report's `resolution_package_json_inputs` gap.

These events exclude `file_module_facts` and automatic type discovery. Complete
retention does not prove a package name, version, peer context, or full graph
identity. Package identities remain missing evidence.

## Source package scopes

The source loader retains its existing package-scope probes, reads, and final
implied-format decisions. Its limit is 16,384 events and 16 MiB of UTF-8 string
data per Program. An omitted event stops further retention. The observation
keeps the prefix and counts all later omissions. Fixed extensions and searches
without a package still have a final decision. Bundled libraries do not make
these package-scope calls.

`sourcePackageScopeObservation` serializes every retained event in order. The
report resolves each event's program-local `FileId` to its loaded source path
in `sourceFile`. It does not infer a source from the package JSON path or
publish a `FileId` as a persistent identity. Read text uses the same VFS parser
input fields as config and resolver inputs. It is not raw disk-byte evidence.
The graph digest includes both package-input reports and their omission counts.

The `source_package_scopes` gap clears only when all observed events and a
matching final format decision for every source that is not a default library
were retained. Other missing-evidence fields remain unchanged. Root and
path-reference loads still do not record filesystem realpaths.

## Selected paths

The report includes `preserveSymlinks` in its explicit resolution options.
Resolved file names are selected lookup paths, not a guarantee that realpath
was called. Original file names remain the lookup candidates before optional
realpath handling. These fields do not close the `source_real_paths` gap.

Nested package imports such as `"#dep": "pkg"` now classify
`externalLibraryImport` from the selected nested target path. A symlink target
outside `node_modules` therefore produces false when symlinks are not preserved.
The 192-case comparison matches pinned Go, with 18 corrected flags and no changes
to Rust paths, host calls, retained inputs, or modes. Earlier input-evidence
reports still describe the commits they tested.

Broader module-resolution differences remain. Under NodeNext, explicitly
disabling package imports blocks `#dep` in Rust but not in pinned Go. For nested
imports without a changed realpath, Go can call `Realpath` again at each outer
resolution, while Rust calls it once. The flag repair does not change those
behaviors or establish full module-resolution or host-call parity.
