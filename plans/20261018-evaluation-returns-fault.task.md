# Evaluation returns its fault (ADR 0013, step 3)

Created 2026-10-18. Status: DONE (pull request #161; no verdict changed; outcome 4 deferred to step 7).
Status file: [status](20261018-evaluation-returns-fault.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D2, "Order" step 3
(depends on step 2), and the D7 note that `Expr.any` comes with this step.

## Pull requests

- **Pull request A (subject):** the model, conformance and tests. No change under `judge/`
  or `integrity/`, and `Contract.lean` does not change: `SupportedSql` keeps its
  statement.
- **Pull request B:** none expected; this step changes no verdict. If a verdict changes,
  stop and report it.

## Outcome

1. **One evaluator with a fault.** Expression evaluation returns its value and a fault
   (`none`, `may`, `must`). A JSON function error is `must` when SQLite reports it
   for certain (malformed JSON, bad path, bad flags) and `may` for a JSONB argument; a
   child's `must` becomes `may` under `AND`, `OR` and `COALESCE`. The predictors
   `Expr.mayFail`, `Expr.mustFail`, `anyFailure`, `describedFailure` and the per-node
   re-application of JSON functions do not exist.
2. **One query run.** A query run gives its result rows with the fault of the query and
   the `SUM` overflow of its groups. `step`, the support check and the statement outputs
   use that run; `Query.fails`, `Query.mayFail`, `Query.mustFail` and `queryJsonReady`
   do not exist as separate evaluations. `JsonFaults.lean` and most of `JsonReady.lean`
   are gone.
3. **One classifier pass.** `classifyCase` and `predict` run the script once and take
   the observation trace, the statement outputs and the support verdict from that run.
   Theorems relate the pass to `runSqlFrom` (as `traceFrom_final` does today) and to
   `supportedSqlFrom`, which the contract's `SupportedSql` keeps.
4. **Readiness returns results.** A write's readiness check that computes the written
   table (`insertReady`, `updateReady`, `upsertReady`) gives that table to execution,
   which does not compute it again.
   Deferred (2026-10-18), by measurement: with one classifier pass, the model suite
   takes 326 s against 335 s before step 3, so the repeated write computation is a small
   part of a case's kernel time, and moving results between `statementReady` (a part of
   the contract's `SupportedSql`) and `literalStep` would couple the two. Step 7, which
   restructures the effects of statements, is the place for it.
5. **Syntactic checks use one traversal.** `Expr.any` (and `Expr.map` where a step needs
   it) replaces `Expr.callsJson`; the remaining syntactic rules (JSON calls in joined
   queries, upsert clauses, RETURNING, `NoWrites`, clock cells) are stated with it.

## Tests

- `just test-full`, `just test-nix` and `just test-scheduled` pass; the scheduled mutant
  suite kills every mutant, with anchors moved to the new code.
- The verdict (`nix-build integrity/judge.nix -A verdict`) has the same counts and
  report as step 2.
- The `#guard` examples of `JsonFaultExamples.lean` keep their expected results,
  restated over the fault of the run.
- `tests.model` time is measured against step 2 (335 s) and reported.

## Key points

- **The fault rules are shape rules today, and they must stay.** The new run must give
  the same support verdict as the predictors for every case:
  - A query with joins or `json_each` sources is unready when any of its expressions
    calls a JSON function, whatever the values (syntactic).
  - `must` counts only for a query without `FROM`, without `LIMIT 0`: the WHERE term,
    an aggregate operand of a passing row (also under OFFSET), and a scalar at
    offset 0.
  - The WHERE term is also evaluated over the empty row `[]` (a constant term runs
    once, even over an empty table); the kept expressions of an aggregate query also
    over `[[]]`; scalars and ORDER BY terms of an aggregate query over every filtered
    row, although the result uses only the first row of a group.
  - `SUM` overflow is a group fault, gated by `LIMIT 0`, and wins over a JSON error in
    `step`.
  - JSONB errors count for `may` only.
- **`json_each` faults are in the source.** `EachSource.join` maps an error to no rows,
  and `eachJsonReady` checks every input row of each source. The source needs its own
  fault, or this check stays.
- **Writes get no JSON error.** A write is supported only when no expression may fail;
  UPDATE and DELETE also check the WHERE term over `[]`. RETURNING and upsert clauses are
  refused syntactically, because execution does not evaluate RETURNING.
- **The resolver uses the predictors.** `Resolution/Assignments.lean` and
  `Resolution/ClockRows.lean` refuse a constant whose JSON call may fail
  (`constantFunctionError`), and `Resolution/QueryExprs.lean` imports `JsonFaults`.
- **The contract keeps `SupportedSql`.** It is `∀ clock, supportedSqlFrom … = true`;
  the demonstrations and `SqlExamples.lean` prove it, some by `decide +kernel`.
- **Mutants.** `json_mutants.json_error_ignored` anchors the `mustFail` line of `step`;
  the `eval` anchors of `number_mutants`, `query_mutants`, `row_write_mutants` and
  `write_mutants`, and the `OBLIGATIONS` texts of `insertReady` and `updateReady`
  (`tests/mutant_guards_test.py`) move with the code.
- **Kernel cost.** The case proofs run the classifier by `decide +kernel`; a pair-valued
  evaluator must not make them slower. Measure one case before and after.
