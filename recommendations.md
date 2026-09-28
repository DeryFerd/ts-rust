# Dev-loop recommendations

From session claude-82, 2026-09-28. Source: an audit of every ts-rust transcript from 2026-09-24 to 2026-09-28 (2 main sessions, 1,220 subagents, 82,711 tool calls). The fixes from that audit landed in `8f64c20ea`. You already recorded the carry-forward rule, accepted R125, archived the closed-batch rule entries and pushed `main`. This file holds what is left.

Theo, 2026-09-28: "I trust all your judgment here. I will give full context so the other agent can decide what it wants to do itself." Each item says what I recommend and why. You decide how, when, and whether to change an item. Record each decision with `scripts/state record note`.

## Items

Work through them in order of your queue. Each item ends on a **done when** line.

### 1. Push rule

**Recommend:** a standing rule in the AGENTS.md "Dev loop" section: push `main` (fast-forward only) after each accepted revision and after each commit that other hosts or agents must test, and push each `goport-*` branch that another host or agent tests. Force pushes stay forbidden. Theo once had to ask "are all the latest things pushed?" before he could send other agents to test.

**Done when:** AGENTS.md has the rule, and `git rev-list --count origin/main..main` is 0 after each accepted revision.

### 2. Prune worktrees

**Recommend:** run `scripts/goport/prune-worktrees.py` (a dry run). Check that no listed worktree belongs to a running workflow or a queued item. Then run it with `--apply`. At 08:30 UTC the dry run listed 254 worktrees and 218 merged branches. Every one is clean, merged into `main`, and idle for 3 days. The script keeps the other 2,597: they have unmerged or dirty work, mostly July agent branches. Keep those, because they may hold unported work.

**Done when:** a new dry run lists 0 stale worktrees.

### 3. Faster builds: parallel frontend, then crate split

`ts_goport` is one crate of 605k lines in 677 files. Sep 24 to 28: 475 release builds (20.4 h, median 81 s, p90 8 min) and 272 fat-LTO `goport` builds (36.7 h, median 7 min). Every edit rebuilds the whole crate.

**Recommend,** cheapest first:
1. Measure a baseline on a quiet host with zbook's CPU (dbook-lan): a clean release build of `ts_goport`, and a rebuild after you touch one checker file.
2. Try the nightly parallel frontend: `RUSTFLAGS=-Zthreads=8` with `cargo +nightly`. Theo accepts experimental Rust. Keep it if the build is faster and the gate still passes.
3. After int12 part 2 lands in `main` (few open lanes then), split the crate (the queue item "Split the `ts_goport` crate"). Map `use crate::` edges first. Move only parts with no edge back into the rest: start with `lsp/lsproto/lsp_generated/`. Measure after each part. Stop splitting when a part gains less than 10% on the touch rebuild.

**Done when:** the before and after build times are in `docs/goport-next.md` (or a linked doc), the gate passes on the result, and every open lane has rebased.

### 4. Adoption gaps

The first 2 hours after `8f64c20ea` (43 subagents) show two gaps:
- Agents called raw `ssh` 53 times and `remote.sh run` 31 times. **Recommend:** workflow prompts use `scripts/goport/remote.sh run auto` for every remote job. Raw `ssh` is only for a quick look.
- The median subagent made 52 calls before its first edit (baseline 43). **Recommend:** check that each new workflow prompt starts with the text of `docs/goport-agent-brief.md`. If it does and the number stays high, list the files agents read before their first edit, and add the facts they keep looking up to the brief.

**Done when:** in `scripts/audit/metrics.py`, `remoteShRun` is higher than `rawSsh`, and `medianCallsBeforeFirstEdit` is at or below the baseline.

### 5. End condition for the known editor-stage FAIL

The gate's editor stage now fails on the known long-session leaks. Treat those failing sessions as known only until the lsmem2 and lsmem3 fixes are in `main`. A new session that fails, or a known one that gets worse, is a regression now. After those fixes, every editor FAIL is a regression.

**Done when:** `docs/goport-next.md` has this end condition, and the gate editor stage passes on `main`.

### 6. Re-audit on 2026-09-30

**Recommend:** add a queue item for 2026-09-30. Then run:

```
scripts/audit/metrics.py --since 2026-09-28T08:10:00Z
```

Compare the result with the baseline below. Targets:

| metric | baseline (Sep 24 to 28) | target |
|---|---|---|
| shortPollsPerSubagentHour | 9.18 | under 1 |
| askUserQuestions (askBlockedHours) | 3 (4.3 h) | 0 |
| formatOnlyRevisions | 1 of 13 (R125; R105 and R114 were also rejected only for rustfmt, but their follow-ups are not labeled format only) | 0 |
| carryForwardRevisions | 0 | every goport-only revision after R125 |
| builds.goport hours | 36.7 | only timing and release builds |
| journalParses / wfstatus | 106 / 0 | wfstatus only |
| rawSsh / remoteShRun | 842 / 546 | rawSsh near 0 (quick looks use `remote.sh look`) |
| medianCallsBeforeFirstEdit | 43 | lower |

`formatOnlyRevisions` also counts a revision that was opened before the window but recorded again inside it. R125 shows up in the first post-change window this way.

For each missed target, find the cause in the transcripts and fix the tool, the brief or the rule. Add one line per finding to this file.

**Done when:** each target is met or has a recorded fix, and `scripts/audit/metrics.py` is committed.

## Considered and not recommended

- **Gate stages in parallel across hosts.** 111 full gates: median 11 min, p90 23 min. Gates now go to free hosts (`remote.sh run auto`). Do this only if integrations wait more than 15 minutes on a gate.
- **More cargo concurrency on zbook.** Since Sep 25 the cargo lock wait has a median of 0 s (0.3 h in total over 227 builds).
- **A Go-to-Rust symbol index.** The 16,728 `// Go: file.go:line Name` markers already make one grep enough.
- **Smaller subagent contexts.** Median 101k tokens per turn. Turn latency grows only a little with size (median 2.8 s at under 100k, 4.0 s at 600k), and Theo said usage does not matter.

## Early numbers after `8f64c20ea` (08:10 to about 10:10 UTC)

Short polls went from 9.18 to 0.31 per subagent-hour. Most subagent waits now use `timeout 590` in one call. Agents called `wfstatus` 10 times and parsed journals 2 times. They called `candidate.sh` 9 times. No agent asked a question. The two gaps are in item 4.

## Decisions (root, 2026-09-28)

1. Push rule: done. AGENTS.md "Dev loop" has "Push"; `origin/main..main` was 0 after R125.
2. Prune worktrees: done. The dry run listed 254 worktrees and 218 branches, none `goport-*` and none used by a script. Applied: 0 stale worktrees left, 1,968 kept. State note `devloop-rec-2-prune-2026-09-28`.
3. Build speed: workflow `devloop-build-speed` measures a stable baseline and nightly `-Zthreads` on dbook, checks output identity, adopts nightly for dev builds only if it is more than 15% faster, and maps the crate split. The split starts after int12 part 2 is in `main`.
4. Adoption gaps: workflow `devloop-agent-onboarding` finds why agents use raw ssh and what they look up before the first edit, then fixes the brief, `remote.sh` and adds a helper if it pays off. The brief now also states the accepted Go pin and the host lock rule.
5. Editor-stage end condition: done, in `docs/goport-next.md`.
6. Re-audit: queued in `docs/goport-next.md` for 2026-09-30, with a session reminder. `scripts/audit/metrics.py` is committed. Early run (since 08:10Z): shortPollsPerSubagentHour 0.3, askUserQuestions 0, rawSsh 53 against remoteShRun 33, medianCallsBeforeFirstEdit 53.
- Also added: AGENTS.md "Workflow changes" (do not resume a workflow after changing a later phase; a resume on 2026-09-28 re-ran 9 finished port lanes), "Pin" (main-based work sets GOPORT_PIN until the default pin switch) and "Host locks" (a subagent ran a job over raw ssh on a locked host during a host move).
- Not done: gate stages across hosts, more cargo concurrency, a symbol index, smaller contexts (as recommended).
- Item 4 follow-up (root): the onboarding workflow (`4c3530ea2`) found that `run auto` never held its lock (ssh closed the fd) and that 0 of 41 new agents used `run auto`, mostly because root prompts named hosts and paraphrased the brief. Fixed: remote.sh `look`, `job`, `push`, `sync-pin`, `status`; `run <host>` locks itself; `scripts/goport/facts`; AGENTS.md now says to paste the brief word for word and name hosts only for timing. Target changed to rawSsh near 0.
