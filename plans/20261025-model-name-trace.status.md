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
