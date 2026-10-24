# ADR 0017 coordination status

Created 2026-10-24. Status: OPEN. ADR 0017 is not complete.
This record coordinates the task/status files; it adds no implementation scope.

## Standing owner instructions

Continue until ADR 0017 is complete. Specify each task before delegating its
implementation to a subagent. Parallel tasks need separate jj workspaces,
disjoint edit surfaces and enough VM resources. Integrate useful modularity
improvements. Push completed task PRs without another permission request.
Clean completed workspaces after the code is pushed, retaining any workspace
needed for an active review. `direnv allow` is authorized. Ask for owner judgment
when a specification is wrong or incomplete, with options and a recommendation.

The 2026-10-24 handoff's check override remains: relevant mutants only by `-k`,
no broad local `test-scheduled` or `test-mutants`; task-end scheduled checking
uses `test-scheduled-checks`. No garbage collection without permission. Keep
10 GiB free on `/` and `/nix/store`. Those share a smaller filesystem than the
workspace filesystem. Reserve at most two heavy build/check processes here.

## Accepted decisions

- S5 default search infers small schemas and targeted values, with explicit
  schemas and custom generators also available.
- S5 background checks are enabled by default. Only a kernel-confirmed
  counterexample is an error; measure and expose the budget.
- ADR 0022 slice 5 splits parent-schema compatibility from row-reference truth.
  Its explicit-mapping primitive and exact engine-selected convenience helper
  preserve the existing SQLite meaning, including repeated key columns.
- ADR 0019 slice 4 supports nonrecursive CTEs. Actual recursion is excluded
  regardless of spelling, and the RECURSIVE keyword remains excluded.

These decisions are in the corresponding tasks. None is pending.

## Active implementation

- `s4_part1`, workspace `sqlite-verifier-s4`: S4 part 1's implementation and
  independent reviews are complete; Nix validation is in progress. The first
  full run caught a duplicate `Connection.queryContext_of_quiet` declaration.
  The agent is replacing it with the existing theorem and rechecking. Parts 2
  and 3 remain required: success/program laws, then removal of `Run.checked`.
  Rebase onto PR #239 or its completed build-boundary successor at a clean
  boundary before part 2. Do not treat part 1 as completion of S4.
- `text_build_boundaries`, workspace `sqlite-verifier-text-build-boundaries`:
  implementation `7d9d7d06` has clean independent review. `just test-full`
  passed with report
  `/nix/store/ykfdsmryx18cplw9zrf1dy3xakqlbydj-sqlite-verifier-test-reports`;
  `just verdict` passed, and all 53 prediction files / 7,372 cases are
  byte-identical to the baseline. `just test-nix` passed 67 tests. The final
  scheduled-check gate and PR handoff are pending at this record's creation.
  Its own status file is authoritative for later results.
- `foreign_key_atoms`, workspace `sqlite-verifier-fk-atoms`: part 1 of
  [the FK task](20261024-foreign-key-atoms.task.md), based on `cf7aa9a6`.
  The agent owns FK atom/check/frame modules, the surface database export and
  their registration entries in the model barrel/lakefile. S4 confirmed these
  entries do not overlap its current work. It has the cached #239 prediction
  baseline `4k77z378vnagzwx5448yqz0686d58cld`. The full pragma statement law
  will reuse S4's query-output bridge after clean integration; part 1 stays
  open until that law and its acceptance checks pass.

The schema and observation helper agents of S4 have completed their reviewed
commits and returned them to S4. Their workspaces remain until pushed cleanup.
No agent may rebase a shared ancestor while another agent is editing a descendant.

## Specified work waiting for its prerequisites

- [S5](20261024-surface-s5.task.md): reviewed; waits for S4's final success and
  run semantics. Plausible v4.34.0 still needs a compatibility build under
  Lean 4.34.1. No dependency is installed yet.
- [Query sources](20261024-query-sources.task.md): review `cf7aa9a6` had no
  findings. Covers derived tables, ordinary CTEs and views, including the
  existing compound-subquery metadata restriction. Reserve model/text files
  before delegation. ALTER/rebuild follows the final view representation.
- [Prediction input filter](20261024-prediction-source-filter.task.md): final
  review `7eb6003e` had no findings. Fixes an observed rerun caused solely by
  Python bytecode; keep it separate from the current build-boundary task.
- [S6 foundations prototype](20261024-surface-s6-foundations.task.md): final
  review `1cd45bae` had no findings. Uses S4's completed monad/universal execution
  interfaces to investigate WP, congruence, the before schema and footprints.
  Full S6 still needs a task after those findings and the model prerequisites.

ADR 0019 slice 5, full S6, S7 and S8 remain to be specified and implemented.
S8's application simulation and the full guide acceptance audit are required
before the ADR 0017 goal can be marked complete.
