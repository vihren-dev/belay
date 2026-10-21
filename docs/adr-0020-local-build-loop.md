# ADR 0020: A local incremental build loop for model work

Date: 2026-10-21. Status: PROPOSED.
Implementation: one task file and one pull request, after the owner decisions below.
Audience: designers and reviewers.
Related: [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md) (Lake builds, one Nix
derivation per Lean package), [ADR 0011](adr-0011-product-trust-and-development-integrity.md)
(the judge; a local result decides nothing), [ADR 0016](adr-0016-model-and-surface.md)
(the model's public roots). Measurements:
[`experiments/dev-loop-cost/README.md`](../experiments/dev-loop-cost/README.md).

## Overview

While an agent edits the model, it checks each edit with a Nix build. Nix builds a Lean
package as one derivation, so each edit to a model module recompiles the whole model
package, then the conformance package. This ADR adds a second way to check an edit: a
local Lake build that compiles only what changed, with the same pinned toolchain, and a
local judge run over the corpora with the runner from that build. Nix stays the only
source of evidence. The local loop gives feedback while an agent edits; the Nix checks
run before each commit, and CI runs them as today.

## Context

### The problem: the Nix build is the edit loop

Measured in the Claude Code development session from 2026-10-09 to 2026-10-21 and on
`main` at 8f6fa3e3 (`experiments/dev-loop-cost/README.md`):

| Measure | Value |
| --- | --- |
| Foreground conformance builds (`nix-build -A conformance` and its recipes) | 462 calls, 5.8 hours |
| `just test-full` | 165 calls, 7.6 hours |
| One edit of `Belay.Sqlite.QueryFunctions`, then `nix-build -A conformance` | 149.6 s |
| The same edit, then a local `lake build conformance-runner` | 24.4 s, 34 jobs |
| The same, after the codec imports only definitions | 9.9 s, 19 jobs |
| A local no-op build | 0.3 s |

The local runner and the Nix-built runner give byte-identical predictions for all 42
judge input files (7,093 cases). A local `python -m judge run` with the local runner
gave the same verdict counts as `just verdict` on the same commit.

The commit `perf: import only the model's definitions in the codec` (on the branch of
this ADR) removes the 30 proof modules from the runner's import closure. This ADR does
not depend on it, but the times above with it are the times of the loop.

### Facts that constrain the design

1. **The dev shell has no Lean toolchain, and its flake cannot get the pinned one.**
   `nix/flake.nix` provides `just`, Python with pytest, the SQLite builds and `patchelf`.
   The pinned toolchain is `leanToolchain` in `build-support/default.nix`. The flake's
   source is the `nix/` directory, so it cannot import `build-support/`:
   `nix eval path:./nix#checks.x86_64-linux.model.drvPath` fails with "access to
   absolute path '/nix/store/build-support/default.nix' is forbidden in pure evaluation
   mode". `nix-build build-support/default.nix -A leanToolchain` gives the same store path
   that the Nix builds use.
2. **`just build` takes over the in-tree build directories.** It replaces
   `.lake/build` and `packages/belay-sqlite/.lake/build` with links into the read-only
   runtime in the Nix store. `just test` and `just test-full` run it first. A local
   `lake build` in `packages/` after that fails: clang reports "Permission denied" for
   each output file under `packages/belay-sqlite/.lake/build/ir`.
3. **A copy of the sources builds incrementally.** With the two packages copied to
   `build/dev-probe/` by `rsync -a --delete --exclude .lake`, a second copy and build
   compiled 0 jobs (0.2 s). A `touch` of a source file compiled 0 jobs, because Lake
   compares hashes. An edit of `Belay.Sqlite.QueryFunctions` compiled 19 jobs. The copy
   of the model and the runner takes 218 MB under `.lake`. `rsync` is on the host, but not
   in the dev shell.
4. **A locally linked runner does not start on NixOS.** Lake links executables for the
   loader `/lib64/ld-linux-x86-64.so.2`, which NixOS does not have; the Nix build fixes
   this with `autoPatchelfHook`. `patchelf --set-interpreter` with the interpreter of the
   toolchain's own `bin/lean` makes a copy of the runner start.
5. **The runner reads no `.olean` files at run time.** A runtime root for
   `python -m conformance.predict --runtime ROOT` needs `lib/`, the parser library
   (`nix-build build-support/default.nix -A parserLibrary.library`), and
   `.lake/build/bin/conformance-runner`.
6. **The judge runs without Nix.** `python -m judge run --root . --claims FILE -- COMMAND`
   gives each claimed corpus's inputs to the command and checks the claims. Its claims
   file maps each corpus name to its claim, so a copy with fewer corpora checks fewer.

## Decision

### D1. No new dev shell; the toolchain comes from the Nix build

The local loop runs in the existing dev shell. It gets the toolchain with
`nix-build build-support/default.nix -A leanToolchain`, under an out-link in `build/`,
so it uses the same store path as the Nix builds. The dev shell gains one package,
`rsync`, for D2.

### D2. A separate local build tree

The local loop copies the Lean packages that it builds from `packages/` to
`build/dev/packages/`, without their `.lake` directories, and runs `lake build` there. It
never writes under `packages/`, so `just build` and the local loop do not interfere. A
copy without changes compiles nothing.

It builds these targets, the ones that model work can break:

| Package | Targets |
| --- | --- |
| `belay-sqlite` | `Belay.Sqlite`, `Belay.Sqlite.Codec` (the targets of `modelPackage`) |
| `sqlite-verifier` | `SqliteVerifier`, `EngineeringExamples` |
| `verifier-conformance` | `conformance-runner` |

The gate's executables, which need `lean4export`, and the documentation tool stay with
Nix.

### D3. A local verdict

A recipe builds the runner as in D2 and makes a runtime root in `build/dev/runtime/`: a
copy of the runner with the loader of D3's fact 4 set on Linux, and `lib/` from the Nix
parser library. It then runs the judge's `run` mode with
`python -m conformance.predict --runtime build/dev/runtime` as the subject, for all
claimed corpora or for the corpora named on the command line. It prints the judge's
counts and failures, writes the report to `build/dev/report.json`, and exits with the
judge's exit code.

The recipe does not change `judge/`, `judge/claims.json` or the lock. For a subset of
corpora it writes a reduced copy of the claims file under `build/dev/`.

### D4. Recipes

| Recipe | Does |
| --- | --- |
| `just dev-build [TARGET...]` | D2: copy and build the targets of D2, or the named ones |
| `just dev-verdict [CORPUS...]` | D3: `dev-build` of the runner, then the local verdict |

Both print where their output is and what to run next when they fail, as the
repository's rule for error messages requires.

### D5. How agents use it

`AGENTS.md` gets a rule for model work: while editing, check edits with the local
loop; before each commit, run the Nix checks that the existing rules require. A local
result is not evidence: commit messages, status files and pull requests cite Nix
results only. This follows ADR 0011: a result on a developer machine decides nothing.

### D6. Tests

The test suite checks the parts that are our code and can be wrong without notice:

- The reduced claims file for a subset of corpora holds the same claims for those
  corpora as `judge/claims.json`, and no others.
- The local runtime root has the layout that `conformance.predict` reads.

A test marked `requires_nix` (outside the Nix suites, because it needs `nix-build` on
the host) runs `just dev-build` twice and checks that the second run compiles no job,
and runs `just dev-verdict` on one small corpus and checks exit code 0. The pull request
records one measurement on the same commit: the counts of `just dev-verdict` equal those
of `just verdict`.

## Consequences

- **An edit of a middle model module costs about 10 to 25 s instead of about 150 s**
  before the agent sees whether the runner still builds. A local verdict over all
  corpora took 95 s on a loaded host (load average about 22 on 8 CPUs).
- **Each jj workspace has its own local tree.** The first `dev-build` in a workspace is
  a clean build: 61 to 102 s for the runner in the measurements. The tree of the model
  and the runner takes about 218 MB.
- **Two ways to build can disagree.** Nothing in the local loop is evidence, and the
  Nix checks before each commit catch a difference. The loop uses the same toolchain
  and the same sources, so a difference shows a bug in the loop.
- **The Nix CI times do not change.** This ADR changes only the agent's edit loop.

## Alternatives considered

**A dev shell that contains the toolchain.** Rejected. The flake cannot import
`build-support/` (fact 1). The flake would need its own copy of the toolchain pin,
which could differ from the one the builds use, or the flake would have to move to the
repository root, so that `nix develop` copies the whole working tree, including
`build/`, into the store.

**Build in place in `packages/`.** Rejected. `just build` replaces the model's build
directory with a link into the store (fact 2), so the local tree breaks after each
`just test`.

**Change `just build` so that it no longer links into `packages/`.** Rejected for this
ADR. The tests that use the in-tree layout would change with it. A separate tree solves
the problem without them.

**Patch the loader at link time with Lake options.** Rejected. `moreLinkArgs` in the
lakefiles would also change the Nix builds, which already use `autoPatchelfHook`.

**Lean Beam for the edit loop.** Not decided here. Its goal-state and lookup commands
could replace some file reads, which the measurements put at a few percent of the
context. It does not build the runner or run the corpora.

## Not decided here

- Running the Python test suites against the local tree.
- Sharing local outputs between workspaces, for example with Lake's artifact cache
  (ADR 0010).
- When Claude Code compacts the context. The owner sets this per user
  (`autoCompactWindow`); it is not repository configuration.

## Owner decisions

To be decided:

1. **The targets of D2.** Recommended: the model, the verifier library with the
   engineering examples, and the runner. The alternative leaves out the verifier library,
   which makes a clean build shorter but lets a model change break the engineering
   examples without local notice.
2. **The rule of D5.** Recommended as written: the local loop while editing, the Nix
   checks before each commit.
