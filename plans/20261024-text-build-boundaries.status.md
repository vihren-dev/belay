# Status: translation dependencies and complete local law checks

Created 2026-10-24. Status: OPEN. Implementation is under validation.
No owner decision is required for the outcomes currently specified.

Task: [task file](20261024-text-build-boundaries.task.md).
Specifications: [ADR 0016](../docs/adr-0016-model-and-surface.md), D2, and
[ADR 0020](../docs/adr-0020-local-build-loop.md).

## Current evidence

Base: PR #239, `srzmyvyu`, commit `98a07bfec142aacec28c0d3f9d4801dd593515f1`.
The task's relevant-file list names the code and existing checks.
`Translation/Located.lean` now imports the existing public root
`Belay.Sqlite.Model.Codec`. This root supplies syntax and restriction declarations
without the model umbrella. The layer check follows transitive imports from
`TranslationProgram`, with direct and indirect import regression cases.
The conformance lakefile defaults to `conformance-runner`; the Nix derivation and
the local `dev-build` recipe now explicitly build `VerifierConformance` and
`conformance-runner`.

Before the edit, `nix-build integrity/judge.nix -A predictions --out-link
build/predictions-before` produced 53 corpus files with 7,372 predictions at
`/nix/store/4k77z378vnagzwx5448yqz0686d58cld-sqlite-verifier-predictions`.
The post-edit comparison and task-end Nix gates are pending.

## Progress

- 2026-10-24: specified the import boundary and the missing local law-library
  check in response to the owner's modularity request. This workspace is
  separate from S4. Task review and implementation are pending.
- 2026-10-24: task review `20261024T115938Z-5fc56924` found no musts and two
  shoulds. The task now states the owner's scheduled-check override and the
  observed law-build failures from the handoff, and removes the proposed
  failure-injection harness. The existing local-loop test remains the check of
  the recipe. Implementation is pending.
- 2026-10-24: review `20261024T120211Z-4d34419d` found no musts and requested
  a durable record of the handoff evidence. The source is the owner-provided
  `/home/codex/work/HANDOFF-adr17-20261024.md`, section "How the work is done":
  "`just dev-build` builds only the conformance runner, not the law modules, and
  `test-full` failed twice because of this." This is a reported observation;
  that handoff supplies no run IDs, so this status does not claim independently
  verified failure logs. The task's target correction is independently supported
  by the current recipe and the Nix library targets recorded above.
  The same source, "Owner rules for this work", says: "Run only the relevant
  mutant tests, by name (`-k`). Never run `just test-scheduled` or
  `just test-mutants` locally; run `just test-scheduled-checks` at the end of a
  task." This is the owner instruction that overrides the older cadence table.
- 2026-10-24: narrowed the translator to the existing public codec root, added
  transitive-import checks to `tests/surface_layers_test.py`, and added the
  complete conformance library to `dev-build`. ADR 0020 lists the corrected
  targets and boundary. No model source, package root, semantic function, claim,
  or judge lock changed. Commit diagnostics use `tests/surface_layers_test.py`,
  `tests/dev_loop_test.py`, and `just dev-build`; Nix acceptance remains pending.

## Local diagnostic procedure

The existing `tests/dev_loop_test.py` runs `just dev-build` twice and requires the
second run to compile no target. The initial build log includes
`VerifierConformance.RunPassLaws`, which is outside the runner's import closure.

The proof-boundary diagnostic temporarily appends
`theorem Belay.Sqlite.Model.buildBoundaryProbe : True := True.intro` to
`packages/belay-sqlite-model/Belay/Sqlite/Model/QueryLaws.lean` and runs
`just dev-build`. Its assertions require recompilation of `QueryLaws` and the
model umbrella and no recompilation of Lean translation modules in the text
package's command. It records native targets separately. A `finally` block
restores the original source; another `just dev-build` checks the restored tree.
The timeout is 1,200 seconds per build. Logs are in
`build/agent-logs/proof-boundary-{build,restored,summary}.log`.
These local diagnostics do not supply semantic acceptance evidence.
