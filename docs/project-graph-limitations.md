# Project graph limits

`Program::project_graph_snapshot` returns the loader's retained facts. It does
not certify that the graph or the canonical module manifest matches upstream.
Its `missing_evidence` field names inputs the loader does not retain.

## Mode-specific module targets

The current `Program::resolved_modules` map uses a containing path and module
specifier as its key. It does not include the request's import or require mode.
Two requests in one file can therefore resolve to different files and overwrite
one map entry. For example, an `.mts` source can contain both of these imports:

```ts
import { value } from "pkg";
import other = require("pkg");
```

If `pkg` has different `import` and `require` export targets, the raw resolver
records contain both targets. The canonical module manifest can still use the
last target for both specifier nodes. This is an existing compiler bug. The
snapshot does not fix it or approve the resulting manifest.

`graph_snapshot_keeps_each_mode_and_unresolved_lookup` checks the raw request
modes and targets. It does not assert that the overwritten manifest target is
correct. A compiler fix needs mode-aware module-map keys and tests against the
canonical checker. Keep that fix separate from read-only graph reporting.

## Missing input evidence

The config resolver does not return its input bytes or its full extends graph.
The retained leaf config text comes from the later diagnostic read. A file can
change between those reads, so that text alone does not prove the config
parser's input.

Module resolution records retain terminal realpaths and package JSON paths.
They do not retain the original path passed to `realpath`, package identities,
or all package-scope inputs. Root and path-reference loads do not request a
realpath. These gaps remain explicit in the snapshot.
