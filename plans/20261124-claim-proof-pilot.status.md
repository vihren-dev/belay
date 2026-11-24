# Status: pilot of the forms of proof for a claim in SQL

Created 2026-11-24.
Status: OPEN.
Task: [20261124-claim-proof-pilot.task.md](20261124-claim-proof-pilot.task.md).

## References

- Owner request of 2026-11-24 (quoted in the task file).
- ADR 0033, `docs/adr/adr-0033-exact-step-rules.md`: the kind rules that the
  pilot uses.
- `docs/development/lean-simplification-goal.md`: how code lines and
  capabilities are counted.
- Fixtures: `tests/surface/Queries/Evaluation/PurgeFrameQueries.lean`,
  `tests/surface/Schema/Tests/PurgeFrameSite.lean`,
  `tests/surface/Programs/Scripts/PurgeFrameClaims.lean`,
  `tests/surface/Schema/Tests/PurgeFrameInstances.lean`.
- Test: `tests/surface_assertion_examples_test.py`,
  `test_purge_frame_claim_over_every_database`.
- Kind rule: `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/PlainDeleteRule.lean`.
- Two-state assertions:
  `packages/belay/Belay/Sqlite/Programs/Claims/TwoStateAssertions.lean`.

## Branches

| Form | Branch | Starts from |
| --- | --- | --- |
| Base | `claim-proof-pilot` | `adr-0033-phase-8-inventory` |
| A, claims in the logic | `claim-proof-pilot-logic` | base |
| B, composable laws | `claim-proof-pilot-laws` | base |
| C, tactic | `claim-proof-pilot-tactic` | B |
| D, checker | `claim-proof-pilot-checker` | base |

## Progress log

- 2026-11-24: task file and status file written. The task file's
  statements about the present code were checked against the revision
  `adr-0033-phase-8-inventory`.
- 2026-11-24, base form: the readiness facts of a row-wise filter
  (`anyMayFail`, `deleteJsonReady`).

## Base form

In progress on the branch `claim-proof-pilot`.

### Readiness facts (model package)

The kind rule `runScriptStep_plainDelete_eq` continues when the clock and
counter checks pass, the table is present, `Resolved.subqueriesPlain` of the
subqueries is true and `deleteJsonReady` is true. The new facts are data
facts. They mention no step.

- `Resolved.anyMayFail_eq_false_iff` (`Queries/Evaluation/QueryPlainLaws.lean`):
  for each context, list of rows and list of expressions, `anyMayFail` is
  false exactly when each expression has the fault `none` over each row. This
  is the general form: an equivalence with no premise.
- `Resolved.anyMayFail_of_rowwise` (`Queries/Evaluation/RowwiseExpr.lean`):
  for each list of row-wise expressions, each context and each list of rows,
  `anyMayFail` is false. The WHERE test of `deleteJsonReady` and both tests of
  `updateJsonReady` have this form, so the fact serves a later UPDATE fact
  too. It leaves out an expression that is not row-wise, for example one with
  a subquery or a function call; for such an expression the equivalence above
  still applies.
- `deleteJsonReady_of_rowwise` (`Schema/Writes/JsonReadyLaws.lean`, new
  module, imported by `Model.lean`): for each optional filter whose
  expression is row-wise, each context, each table and each list of
  RETURNING columns, `deleteJsonReady` equals the RETURNING check alone. With
  no RETURNING it is true. It leaves out a filter that is not row-wise.
- The clock and counter conditions come from `Resolved.Statement.Calm`
  (`Calm.readsClock`, `Calm.firstUnknown`) and `Resolved.Expr.Rowwise.calm`;
  `Resolved.subqueriesPlain []` is true by computation. No new fact is needed
  for them.
- No package theorem states that the step of a DELETE continues (ADR 0033,
  D7).

Elaboration time of the changed model modules (`lake env lean`, lower of two
runs, local): `QueryPlainLaws` 1.98 s, `RowwiseExpr` 0.46 s,
`JsonReadyLaws` 0.26 s.

Checks (local): `just dev-build` passed.

## Form A

Not started.

## Form B

Not started.

## Form C

Not started.

## Form D

Not started.
