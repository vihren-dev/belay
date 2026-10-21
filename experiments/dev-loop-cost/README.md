# Time and token cost of the development loop

Question: which changes make model development faster and use fewer tokens?

Measured 2026-10-21 on one Linux x86_64 host (8 CPUs, shared with other sessions:
load average 8 to 11 during the runs), Lean and Lake 4.34.1, at `main` 8f6fa3e3.
The token data comes from the transcript of the Claude Code development session from
2026-10-09 to 2026-10-21. This file gives aggregate numbers only.

## How to reproduce

```sh
LAKE=$(readlink -f build/conformance/lean)/bin/lake
python3 -I experiments/dev-loop-cost/token_drivers.py SESSION.jsonl SESSION/subagents
python3 -I experiments/dev-loop-cost/import_graph.py packages/belay-sqlite packages/verifier-conformance \
  --closure ConformanceRunner --marker Laws
python3 -I experiments/dev-loop-cost/rebuild_bench.py packages/verifier-conformance conformance-runner "$LAKE" \
  packages/verifier-conformance/VerifierConformance/Json.lean packages/belay-sqlite/Belay/Sqlite/QueryLaws.lean \
  packages/belay-sqlite/Belay/Sqlite/QueryFunctions.lean packages/belay-sqlite/Belay/Sqlite/Identifier.lean
python3 -I experiments/dev-loop-cost/compare_predictions.py . INPUT_DIR build/conformance LOCAL_RUNTIME
```

`INPUT_DIR` is the output of the judge's `inputs` command (42 files, 7,093 cases).
`LOCAL_RUNTIME` is a copy of the `build/conformance` root whose
`.lake/build/bin/conformance-runner` is the local Lake build. On NixOS, set the local
binary's loader to the one of the Nix-built runner first (`patchelf --set-interpreter`,
in the dev shell). Without this step the binary does not start.

## Token use

| Measure | Value |
| --- | --- |
| API requests (deduplicated by request id) | 10,400 |
| Cache-read tokens | 5.3 billion |
| Share of the weighted cost: cache read, cache write, output | 82%, 12%, 7% |
| Context per request: median, 90th percentile | 518,558, 873,086 |
| Compactions | 17 |
| Context when a compaction starts (median) | 966,312 |
| Subagent cost, as a share of the main session | 2.5% |

The weights are list-price ratios: a cache read costs 0.1, a one-hour cache write 2,
and an output token 5 uncached input tokens.

What stays in the context ("resident tokens": the tokens of an item times the number
of later requests that read it again, until the next compaction):

| Source | Tokens added | Share of all context read |
| --- | --- | --- |
| Results of file reads and searches | 2.4 M | 15.3% |
| Shell commands that the agent wrote (scripts, heredocs) | 2.4 M | 13.0% |
| Results of Python and pytest commands | 0.5 M | 3.1% |
| Files written with `Write` | 0.5 M | 3.1% |
| Results of `jj`, `git` and `gh` | 0.3 M | 1.8% |
| Results of Nix builds and tests | 0.2 M | 1.4% |
| Results of `lake` and `lean` commands | 0.1 M | 0.5% |
| Results of `just review` | 0.1 M | 0.4% |

Simulations over the same requests, with the recorded growth between requests:

| Change | Context tokens, share of real |
| --- | --- |
| Compaction at 200,000 tokens | 27% |
| Compaction at 300,000 tokens | 37% |
| Compaction at 500,000 tokens | 54% |
| A new session at each prompt of 50 or more tokens | 90% |
| A new session at each prompt, including "yes" | 48% |

The compaction simulation starts each segment at the median summary size (52,028
tokens), adds one request at the threshold for each compaction, and adds 30,000
tokens for files that the agent reads again. It cannot measure the quality cost of
a summary that leaves out detail.

## Time

Tool time in the same session, by command (foreground calls only; a background
call returns at once and its time is not counted):

| Command | Calls | Hours | Mean seconds |
| --- | --- | --- | --- |
| `just test-full` | 165 | 7.6 | 166 |
| `nix-build -A conformance` and conformance recipes | 462 | 5.8 | 45 |
| `just review` | 490 | 6.9 | 51 |
| `just verdict` | 99 | 2.3 | 85 |
| `just test` | 109 | 2.1 | 69 |
| `lake` and `lean` | 510 | 0.9 | 6 |

### A local Lake build of the conformance runner

`lake build conformance-runner` in `packages/verifier-conformance`, with a one-line
definition appended to one module and then removed. Job counts are exact. Times
vary with the load of the host.

| Edited module | Jobs | Seconds | Nix, same edit |
| --- | --- | --- | --- |
| None (no-op) | 0 | 0.3 | 1.5 |
| `VerifierConformance.Json` (runner) | 5 | 5.7 | |
| `Belay.Sqlite.QueryLaws` (proofs) | 10 | 14.4 | |
| `Belay.Sqlite.QueryFunctions` (middle) | 34 | 24.4 | 149.6 |
| `Belay.Sqlite.Identifier` (162 dependents) | 165 | 74.9 | |
| Clean build (4 runs) | 367 | 61 to 102 | |

The local runner and the Nix-built runner give byte-identical predictions for all
42 input files (7,093 cases), in about 25 s each.

### Proof modules in the runner's import closure

The runner imports `Belay.Sqlite.Codec`, and the codec imports the model's root
`Belay.Sqlite`, which imports every `...Laws` module. `Belay.Sqlite.Resolution`
imports the `...Spec` modules. So 30 proof modules are in the closure of a program
that only runs definitions. When the codec imports the 25 definition modules of the
two roots instead, the closure has 150 modules instead of 182 and no proof module.
The codec then needs one change: its module docstring cannot use a checked
reference to the root.

| Edited module | Jobs, root import | Jobs, narrowed | Seconds, narrowed |
| --- | --- | --- | --- |
| `VerifierConformance.Json` | 5 | 5 | 3.9 |
| `Belay.Sqlite.QueryLaws` | 10 | 0 | 0.2 |
| `Belay.Sqlite.QueryFunctions` | 34 | 19 | 9.9 |
| `Belay.Sqlite.Identifier` | 165 | 133 | 31.7 |
| Clean build | 367 | 303 | 47 to 84 |

The sum of module compile times in a clean build goes from 311 s to 235 s in the
least loaded runs. The narrowed runner gives the same predictions for all 42 files,
and `nix-build -A runtime -A conformance` succeeds, so the verifier library and the
gate still build. The Nix build does not gain from it now: `modelPackage` builds the
whole model package as one derivation, proofs included.

### Lean Beam

Not tried. Lean commands are 0.5% of the context and 0.9 hours of tool time, so a
faster or more compact Lean check cannot change the totals. An earlier estimate of
3% to 6% counted every command that named a `.lean` file as a Lean command.

## Findings

1. **Compaction late in a 1M-token context is the main token cost.** The median
   request reads 518,558 tokens, and a compaction starts at about 966,000. Earlier
   compaction (at 200,000 to 300,000 tokens) would read 27% to 37% of the tokens.
   A new session per task saves little (10%), because one task fills the context.
2. **Reads and agent-written scripts are the largest items in the context.** Whole-file
   reads and long heredoc scripts stay until the next compaction. Bounded reads
   (line ranges, counts) and edits with `Edit` instead of Python rewrite scripts
   reduce them.
3. **The Nix conformance build is the edit-loop cost.** A middle-of-model edit takes
   150 s with Nix and 24 s (10 s narrowed) with local Lake, with identical predictions.
   An agent can use the local runner while it edits and the Nix build before a commit.
4. **The codec's root import puts proofs into the runner.** Narrowing it removes 30
   proof modules from the closure and halves the rebuild after many model edits.
   It agrees with ADR 0016 D2, which keeps the codec as a public root.
