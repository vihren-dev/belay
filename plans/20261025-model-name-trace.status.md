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
- 2026-10-26: layer 3 done in the working copy: the sources of `FROM` with the trace.
  `resolveTableReferenceTraced`, `resolveReferenceTraced`, `resolveSourcesTraced`,
  `mergeJoinTraced` and `mergedNamesTraced` record the schema, the table (as a source, or as a
  missing name with the tables and views of the catalog as candidates, or as refused), the alias
  and the names of `USING`, with the old functions as projections. Facts at creation: a
  `ScopeSource` now holds its `role` (`SourceKind`) and its `catalogPosition`; `Scope.singleAt`
  and `tableScope` carry the position. Review 12 of the layer-2 refactor gave one should (catch-all
  matches over `NameResult` in the examples), fixed here. Kernel examples:
  `NameTraceSourceExamples.lean`. Proof repairs of layer 3: 27 manual changes (the four theorems
  of `JoinMerge`, `QuerySourceCopyLaws` 2, `QuerySpec`, `SimpleSourceResolution` 2,
  `SimpleStatementResolution` 2, `ExprResolutionLaws`, `DuplicateKeyResolution` 3,
  `ScalarSubqueryResolution` 4, `TableInfoResolution`, `NormalizedFieldLookups` 3,
  `NormalizedFieldSelectResolution` and `NormalizedFieldResolution` 4 corollaries of new `_at`
  lemmas). Total so far: 48 manual and 42 mechanical changes (90 together). Gaps found: a
  view or `WITH` use `FROM v AS v` records the table only (the alias equals the table name).
- 2026-10-26: layer 4 done in the working copy: subqueries, compound queries and the copied
  definitions with the trace. `resolveSelectTraced`, the subquery steps, `resolveCompoundOrderBy`,
  `expandCommonTablesTraced` and `resolveAllFromTraced` have the old functions as projections. The
  trace of a select is settled (`NameTrace.settled`): a name that two passes of the resolver reach
  gives one record, keyed on path, role and exactness. The statement level does not settle,
  because two uses of one WITH definition must stay two records. Source-kind refinement:
  `CommonTableCopies.definitionKinds` tells which derived table is a stored view (`storedView`, with
  its catalog position) or a copy of a WITH definition (`commonTable`); `originalSource` and
  `originalOccurrence` map the copy back to the definition as written, and
  `CommonTableCopies.declarations` records the name and column list of each used WITH definition at
  `[field, origin, 12, 0]` and `[field, origin, 12, 1, k]`. Proof repairs of layer 4: about 7 manual
  (`QuerySpec`, `SimpleStatementResolution`, `SimpleSelectResolution`, `SubquerySelectResolution`,
  `ResolveStatementForms`).
- 2026-10-26: write layer done in the working copy: `resolveInsertTraced`, `resolveUpdateTraced`,
  `resolveDeleteTraced`, the upsert and RETURNING resolvers, `resolveWriteSubqueriesTraced` and
  `resolveCommonTableWriteTraced`, each with the old function as its projection. `Traced.stage` and
  `Traced.withTarget` (`WriteStages.lean`) run the stages of a write and record the target table.
  Paths: INSERT table 0, column list `[1, k]`, rows `[2, r, c]`, conflict clauses `[3, j, ...]`,
  RETURNING 5, subqueries 6; UPDATE table 0, assignments `[1, k, 0|1]`, filter 2, RETURNING 3,
  subqueries 4; DELETE table 0, filter 1, RETURNING 2, subqueries 3. The proposed row `excluded`
  of an upsert has the kind `proposedRow` and the catalog position of the written table. Proof
  repairs of the write layer: about 18 manual (`UpdateSpec` 2, `WriteCatalogSpec` 5, `RowSpec` 1,
  `PrepareSpec` 2, `ResolveStatementForms` 5, `NormalizedFieldUpdateResolution` 2,
  `ResolveStatementFacts` 1) and 57 mechanical lines (`resolveStatement` in a simp list became
  `statement_arms`). New lemma modules (not repairs): `WriteTracedLaws`, `StatementArms`.
- 2026-10-26: statement entry point done in the working copy: `resolveStatementRun` (per constructor;
  DDL and PRAGMA through `Traced.lift`), `resolveStatementTraced` (the run with the constraint
  post-pass `NameTrace.withConstraints`, which fills primary key, UNIQUE and foreign key from the
  table at the catalog position of the source), `resolveStatement` as the first component, and the
  theorem `resolveStatementTraced_fst` (the projection law, by `rfl`). Kernel examples:
  `NameTraceStatementExamples.lean` and `NameTraceWriteExamples.lean`. Surface check:
  `tests/surface/NameTraceSpans.lean` with `tests/surface_name_trace_test.py`.
- Proof repair totals: 73 manual and 99 mechanical changes. The count of manual changes
  stays below the limit of about 80.

## Documented gaps (found in the work)

- CREATE TABLE, CREATE INDEX, CREATE VIEW, CREATE TRIGGER and ALTER bodies, and stored trigger
  programs; the trigger-row scope sources have the default role and are not traced.
- Unused WITH definitions, star-expansion columns, RETURNING `*` columns, function names and
  collation names.
- A CTE body that the resolver copies for each use is recorded once for each use (same path).
- `FROM v AS v` records the table only.
- Names inside the view body that a write to a view reads (`viewColumns`, `resolveViewTarget`).

## Import boundary of the simp sets (2026-10-26)

`tests/test_model_package.py::test_root_imports_the_core_and_only_the_prelude` failed since layer 1:
ADR 0006 lets the core import `Init` only, but `register_simp_attr` (the simp sets `traced_drop`,
`traced_arms`, `statement_arms`) needs `import Lean.Meta.Tactic.Simp.RegisterCommand`. The owner
decided on 2026-10-26 to allow exactly this module. ADR 0006 has a dated amendment and the test
allows this one module (commit `refactor: allow the module that registers simp sets in the model
core`). Two core modules import it: `Resolution/TracedAttr.lean` and `Resolution/StatementAttr.lean`.
Two other faults of the same test are fixed in the layer-4 commit: `Model.lean` no longer imports
compiled examples (Lake builds them through the `Resolution.*` glob), and `lakefile.toml` lists the
module `SingleSourceNameLaws`.

## Review results of the final commits

- Decision commit (`b660aab9`, review 15): no findings.
- Layer-4 commit (`c206e9b4`, review 16): one must (R11). `NameTrace.settled` merged the two
  comparison records of a `BETWEEN`, which have one path and one role. Fixed in the next commit: the
  form of the comparison is part of the key, with examples at the settled level and the statement
  level.
- Fix commit (`ca5e6f1d`, review 17): no findings.
