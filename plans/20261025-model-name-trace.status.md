# Status: model name trace

Created 2026-10-25. Status: OPEN.
Task: [task file](20261025-model-name-trace.task.md).
Specs: ADR 0017 S1 editor requirements; [editor task](20261024-surface-editor.task.md).

## Starting point

Workspace `sqlite-verifier-name-trace` starts at `e196e661`, the S6
before-context integration (PR #265). The editor's interface notes are in the
task file. Relevant sources: `Resolution/Resolve.lean`, `Resolution/ScopeNames.lean`,
`Resolution/QueryAffinity.lean`, `Resolution/CommonTableCopies.lean` and
`belay-sqlite-text/Belay/Sqlite/Translation/Located.lean`.

## Progress log

- 2026-10-25: task and status files written.
- 2026-10-25: review 1 of the task commit (`6335c706`) gave four must findings
  (CTE copies and `exact`, quote kind of qualified names, CAST affinity, the
  prediction-file comparison). The task file now states each of them as the code
  has it. Findings are recorded as fixed.

- 2026-10-25: review 2 (`c088b934`) gave two musts: the trace is computed
  beside the resolver, not in its run, which the editor task states otherwise;
  and compound ORDER BY must be covered. The task file now records the decision
  for the walk beside the resolver, the editor task gets a dated note, and the
  gap list no longer has compound ORDER BY.

- 2026-10-25: the coordinator found that the walk beside the resolver weakens
  the task's main guarantee, so it is the owner's decision. The "decision"
  wording in both task files now reads "proposed, pending the owner's
  decision". Until the answer arrives, only work that both designs need
  continues: the data types, translator span parts and their path test,
  kernel fixtures, the prediction baseline and the conformance-input
  agreement harness. The walker modules (`NameTraceBinding` to
  `NameTraceStatement`) are written but held back, not committed.

- 2026-10-25: prediction baseline built from the base tree in a clean workspace
  (`build/predictions-baseline`, Nix store output
  `/nix/store/r1aksjg6av55bcs82fnlard7gsqi5ndk-sqlite-verifier-predictions`): 55 files
  (`corpus-v1` to `corpus-v54` and `synthetic-workload`), not the 53 that the
  coordinator named.
- 2026-10-25: a probe of the translator's spans (both designs need it) shows that the
  existing parts already select the name tokens at every path of the plan: unqualified
  and qualified column names, schema parts, table, alias and schema parts of a table
  reference, `x.*` qualifier, `USING` names, `ORDER BY`, `GROUP BY`, `HAVING`, write
  assignment names, insert column list, conflict target and assignments, `RETURNING`
  and the name and column list of a `WITH` definition at `[8, i, 12]`. No
  `belay-sqlite-text` change is planned. Function names and collation names have a
  span but are not traced.
- 2026-10-25: data types `Resolution/NameTraceTypes.lean` imported from `Model.lean`.
  The walkers were written and checked as a trial (about 900 lines in nine modules) and
  are held back, uncommitted, until the owner decides between the two designs.
- 2026-10-25: review 5 (`4ddbbd41`, data types) gave one must: the file had 207
  lines. It now has 199; recorded as fixed.
- 2026-10-25: review 6 (`c483d59e`, refactor) found nothing. Work stops here until the
  owner decides; the held walker modules are in `build/held-walkers/` (not tracked).

## Implementation plan (informal)

- Do not change `resolveStatement` or the resolver functions that proofs unfold
  (57 unfold sites in 43 files). `resolveStatementTraced` returns
  `(resolveStatement ..., trace)`, so the law holds by `rfl`.
- New modules `Resolution/NameTrace*.lean`, each below 200 lines, imported from
  `Model.lean`: (1) data types; (2) expression walker over `Scope.resolveName`,
  `comparisonAffinity` and `comparisonCollation`; (3) query and source walker
  with the resolver's scope functions; (4) write statements; (5) entry points
  and agreement theorems.
- Tests: kernel `#guard` examples; a Lean surface fixture and pytest check that
  each exact path selects the name token; a check over the frozen conformance
  inputs that dropping the trace equals `resolveStatement`.
- Agreement checks: see the task file, "The trace uses the resolver's own decisions".
- Prediction files: baseline built before the first model change
  (`build/predictions-baseline`), compared after each model commit.

## Documented gaps (planned)

- CREATE TABLE, CREATE INDEX, CREATE VIEW, CREATE TRIGGER and ALTER bodies.
- Unused WITH definitions (the resolver never resolves them).

Compound ORDER BY terms are in the coverage (`resolveCompoundOrderBy` resolves
them through result-alias lookup and `resolveOperand`).
