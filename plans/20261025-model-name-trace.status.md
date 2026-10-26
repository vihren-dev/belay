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
  the task's main guarantee, so the owner decided it.
- 2026-10-26: the owner decided to thread the trace through the resolver. The
  walk beside the resolver is rejected. The task files now state that decision,
  the returned shape (the result paired with a trace that is also given on
  failure), the projection law as a theorem, and that proof repairs are the cost.
  The test over the frozen conformance inputs is dropped (see the task file).
  The held walker modules in `build/held-walkers/` are a source of record-building
  code only and are deleted before the task ends.

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

- A traced form for each resolver function that leads to a name decision; the
  untraced function is its projection. Order: the trace monad and the
  projection lemmas, `resolveOperand` and its mutual functions, the clause and
  source resolvers, subqueries and compounds, the write resolvers, then
  `resolveStatementTraced` and the projection law.
- Proof repairs are counted here. Layer 1 (the monad `Traced` and the operand
  resolution): 5 manual changes (a `rw` that used the old equation of
  `resolveOperand` or `resolveArguments`, now the equation lemmas
  `resolveOperand_arm_call` and `resolveArguments_arm_cons`; the negation arm of
  `ResolveReadsBelow`) and about 42 mechanical line changes (`resolveOperand` in a
  simp list became `traced_arms`). Total so far 47 of the limit of about 80.
- Tests: kernel `#guard` examples; a Lean surface fixture and pytest check that
  each exact path selects the name token.
- Prediction files: baseline `build/predictions-baseline` (55 files), compared
  after each model commit.

## Documented gaps (planned)

- CREATE TABLE, CREATE INDEX, CREATE VIEW, CREATE TRIGGER and ALTER bodies.
- Unused WITH definitions (the resolver never resolves them).

Compound ORDER BY terms are in the coverage (`resolveCompoundOrderBy` resolves
them through result-alias lookup and `resolveOperand`).

- 2026-10-26: layer 1 done in the working copy: `Traced` (the monad with the trace
  that survives errors), the operand resolution threaded with the trace
  (`resolveOperandTraced`, `resolveArgumentsTraced`, `resolveCaseTraced`),
  `resolveOperand` and its mutual functions as their projections, the arm
  equations (`traced_arms`) that the old proofs use, and kernel examples
  (`Resolution/NameTraceExamples.lean`). `SourceRef.index` is the position among
  the sources of the same depth (the position in the `FROM` list). The full model
  and `just dev-build` pass.
- 2026-10-26: layer 2 done in the working copy: the traced forms of the clause
  resolvers (`resolveQueryBodyTraced`, `resolveResultColumnTraced`,
  `resolveAggregateCallTraced`, `resolveGroupTermTraced`, `resolveOrderTermTraced`,
  `resolveJoinConditionTraced`, `resolveEachArgumentsTraced`, `resolvePendingSourcesTraced`,
  `sourceStarColumnsTraced`) with the old functions as projections, the list helpers
  `resolveAllTraced` and `Traced.keepOnFailure` (`TracedList.lean`), the arm equations
  (`QueryBodyArms`, `ResultColumnArms`, `QueryAggregatesArms`, `SourceListArms`) and kernel
  examples for aliases, aggregate operands, GROUP BY candidates and failure traces
  (`NameTraceQueryExamples.lean`). The names inside aggregate calls are recorded by the operand
  pass at the paths of the operands; the separate pass that lists the calls keeps its trace only
  when it is the one that fails. Review 10 of the layer-1 refactor gave two musts (a catch-all match
  on `Candidate`; no example with alias candidates), fixed here. Proof repairs of layer 2: 16
  manual changes (arm lemmas for `resolveQueryBody`, `resolveResultColumn`,
  `resolvePendingSources`, `resolveJoinCondition`, `resolveAggregateCall`, `resolveGroupTerm` in
  eight proof files). Total so far 63 of the limit of about 80. The `if let` over the joins of
  a query became `aliasJoinItem?`, so that the projection can be pushed through it.
