# Status: syntax and resolution core, step 1a of ADR 0008

Created 2026-10-10. Status: IN REVIEW.
Task: [task](20261010-syntax-resolution-core.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/`,
`packages/belay-sqlite/lakefile.toml`, `conformance/requirements-3.51.0.json`.

## Findings

- Dependents of the replaced model (survey, 2026-10-10): about 1,100 lines of
  theorem and example bodies use `Schema`, `Statement` or `runSql`; the gate
  names the generated declarations in `GateCore.expectedTarget`; the bundle
  checker builds `nextSchema`, `script` and `profile` from the structural
  record; Python computes `nextSchema` with `transition`; 8 approved files
  mention the replaced names, and their `baseline.json` hashes are written by
  hand.
- Baseline build times on `main` (`5a813d20`), forced rebuild with
  `nix-build --check` in the sandbox, Linux amd64: `modelPackage` 7 s,
  `leanRuntime` 13 s, `conformanceRuntime` 17 s, `publicDocumentation` 5 s.

## Progress

- 2026-10-10: PR #79 merged first (owner decision). Task and status files
  created in the jj workspace `adr8-step1`.

- 2026-10-10: the Lean core layers, all in `packages/belay-sqlite/Belay/Sqlite/`:
  `Profile`, `Syntax`, `Catalog` (affinity and rowid alias rules), `Resolved`
  (prepare errors with SQLite's message formats, model restrictions),
  `ResolveValues`, `ResolveDefinitions`, `ResolveWrites`, `Resolve`, and the
  specification modules `ResolveSpec` (column reference), `ResolveRowSpec`
  (row width), `ResolveCatalogSpec` and `ResolveNamesSpec` (unique names, per
  statement and per script), `ResolveErrorKinds`, `ResolvePrepareSpec`,
  `ResolvePrepareRules` and `ResolveDefinitionRules` (prepare errors for
  missing and used names, both directions, for every statement),
  `ResolveTransactionSpec` (catalog after ROLLBACK): 51 theorems. `ResolveExamples` has 30
  `#guard` checks. `LiteralData.lossless` takes an affinity, so the old model and
  `resolve` share it. The prepare checks follow the order of the 3.51.0
  functions `sqlite3StartTable`, `sqlite3AddColumn`, `sqlite3AddPrimaryKey`,
  `sqlite3CreateIndex`, `sqlite3AlterBeginAddColumn`,
  `sqlite3AlterFinishAddColumn`, `sqlite3MultiValues`, `sqlite3Insert` and
  `sqlite3Update`, read in the vendored `parser/upstream/sqlite3.c`.
- Findings from the SQLite source: the first error wins, because
  `sqlite3RunParser` stops at the first error; the rowid alias needs the
  declared type exactly `INTEGER` (`COLTYPE_INTEGER`, case-insensitive after
  dequoting) and no `DESC` in the column constraint, while a table
  `PRIMARY KEY (x DESC)` is still an alias; `DEFAULT name` stores the name as
  text; COMMIT and ROLLBACK without a transaction fail at step, not at prepare.

- 2026-10-10: commit `aeed622a`. Review `20261010T184131Z-aeed622a`: 18 must
  findings (R1, R2, R3, R5, R6), all fixed in `9bd0fb3d`: the resolution modes
  are a catalog description and statements that the execution semantics runs,
  so the model has no migration concept (R6); every match lists its
  constructors; the modeled defaults and integer-comparable affinities are named
  predicates in `ResolveContext`; four docstrings state their formulas exactly;
  every reused or long proof has a sketch. Review `20261010T184626Z-9bd0fb3d`:
  one should finding, restriction messages without a next step, fixed for all
  messages in `f4e4589a`. Review `20261010T184815Z-f4e4589a`: two should
  findings (affinity advice, no check of the messages), fixed in `351528d5`,
  whose review has no findings.
- 2026-10-10: checks. `just test-source`: 461 passed; all ten Nix test suites
  pass (284 s wall); `apiReferenceBase` and `publicDocumentation` build.

- 2026-10-11: owner comment on PR #81 (`Belay/Sqlite.lean` line 30, the long
  list of resolution imports): "Isn't there a better way?". The 20 modules move
  to `Belay/Sqlite/Resolution/` without the `Resolve` prefix (for example
  `ResolvePrepareSpec` is now `Resolution/PrepareSpec`). `Belay.Sqlite.Resolution`
  imports them; the root imports only it, and the package lakefile builds them
  with the one glob `Belay.Sqlite.Resolution.*`, so a new resolution module
  needs no lakefile or root change. All 20 modules compile, including the
  examples, which no module imports. Rebased onto `main` (`60f71de`) first.

## CI time (Linux amd64, forced rebuild with `nix-build --check`, one run each)

| Target | `main` (`5a813d20`) | This branch | Change |
| --- | --- | --- | --- |
| `modelPackage` | 7 s | 16 s | +9 s |
| `leanRuntime` | 13 s | 17 s | +4 s |
| `conformanceRuntime` | 17 s | 21 s | +4 s |
| `publicDocumentation` | 5 s | 6 s | +1 s |
| `apiReferenceBase` | 29 s | 37 s | +8 s |

No test file changes, so the test suites run the same tests. A CI run that
changes no Lean source reuses all these builds. A run that changes Lean sources
rebuilds them; the new modules add about 10 to 20 s to such a run, depending on
how the builds overlap. Single runs on a shared machine vary by a few seconds.

## Remaining

- Owner review of the pull request, then step 1b.

- 2026-10-12: Prepared a local integration of original PR head `805c37ca`
  with accepted main `ee6185ce`, in the reused completed `ci-time`
  workspace. Its previous checkout is retained by an archive bookmark.
  The integration has no conflict. All 596 main review records retain
  their bytes; 26 branch review records are added. Trust-boundary files
  are unchanged against main. The model package, Lean runtime and complete
  runtime build successfully on macOS. The documentation inventory checks
  all 482 authored declarations. Source acceptance passes 492 tests and
  58 subtests in 72.00 seconds, with two expected Linux-only pidfd skips.
  The initial run used an unbuilt checkout root and failed fixture setup;
  its XML is retained separately and is not counted as acceptance.
  The corrected run selects the built complete runtime. Build identities,
  logs and source XML remain local under `build/20261012-syntax-integration/`
  and `build/test-results/`. Original PR #81 remains at its reviewed head;
  this local integration has not been pushed or merged.

Decisions waiting for the owner:

- Final review of PR #81 before step 1b. The local integration is prepared
  for that review and still needs its independent integration review.

- 2026-10-12: Local integration `013c880d` passes independent review
  `20261012T080822Z-013c880d` with no findings. The integrated source is
  checked on macOS within the build and source scopes above. Publishing
  this integration will provide a current-main head for hosted checks and
  final owner review. No step 1b switch or owner acceptance is claimed.

Decisions waiting for the owner:

- Final review of PR #81 after hosted checks at the integrated head.

- 2026-10-12: Merge `2ab3f2fb` brings `main` at `6441fc14` (ADR 0011
  proposal, #90) into the branch without conflicts. It adds one document and
  three review records and changes no source or test file. Review
  `20261012T090836Z-2ab3f2fb` has no findings.
