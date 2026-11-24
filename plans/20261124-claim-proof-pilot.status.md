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
- 2026-11-24, base form: review fixes of the readiness facts (the
  docstring of `anyMayFail_eq_false_iff`, the reach of the UPDATE checks).
- 2026-11-24, base form: the weaker site, `purge_continues` and the frame
  client statement over the catalog of `sessions`.
- 2026-11-24, base form: review fixes of the frame commit (docstrings in
  short sentences, the fields of `sessionsSite`).
- 2026-11-24, base form: the effect claim `purgeClears` and its client
  statement `purge_clears`.
- 2026-11-24, base form: review fixes of the effect commit (declaration
  names in module docstrings as plain code, the proof sketch of
  `purgeClears_iff`, the docstrings of the instances and of the test).
- 2026-11-24, base form: `PurgeEffectClaims.lean` and
  `PurgeFrameSchema.lean` name their declarations with checked references,
  in a second module docstring at the end of the file. Lean refuses a Verso
  module docstring after a Markdown one, so `set_option doc.verso true` now
  comes before the first module docstring.
- 2026-11-24, base form: `PurgeFrameSite.lean` gets the same layout, with a
  checked reference to `PurgeFrameSite.purge_continues` at the end.
- 2026-11-24, base form: the first module docstring of `PurgeFrameSite.lean`
  no longer names the structure; the last one names it with a checked
  reference.

## Base form

In progress on the branch `claim-proof-pilot`.

### Readiness facts (model package)

The kind rule `runScriptStep_plainDelete_eq` continues when the clock and
counter checks pass, the table is present, `Resolved.subqueriesPlain` of the
subqueries is true and `deleteJsonReady` is true. The new facts are data
facts. They mention no step.

- `Resolved.anyMayFail_eq_false_iff` (`Queries/Evaluation/QueryPlainLaws.lean`):
  for each context, list of rows and list of expressions, `anyMayFail` is
  false exactly when each listed expression, evaluated in the context over
  each listed row, has the fault `none`. This is the general form: an
  equivalence with no premise.
- `Resolved.anyMayFail_of_rowwise` (`Queries/Evaluation/RowwiseExpr.lean`):
  for each list of row-wise expressions, each context and each list of rows,
  `anyMayFail` is false. The WHERE test of `deleteJsonReady` and the WHERE
  and SET tests of `updateJsonReady` have this form, so the fact serves a
  later UPDATE fact too. The RETURNING test of `updateJsonReady` is a
  separate test that this fact does not cover. The fact leaves out an
  expression that is not row-wise, for example one with a subquery or a
  function call; for such an expression the equivalence above still applies.
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

Checks run, local outcome only, not evidence: `just dev-build` passed
(local).

### The weaker site and the frame client statement (fixtures)

- `PurgeFrameSite` (`tests/surface/Schema/Tests/PurgeFrameSite.lean`) has
  only the database as its parameter. The field `purgeModeled` is removed;
  the values of the parameters are no longer part of the site.
- `PurgeFrameSite.purge_continues` (same file, a client lemma, not a package
  theorem): for each site, environment and pair of values, the step of the
  purge continues. Its proof applies `runScriptStep_plainDelete_eq` with
  `Resolved.Statement.Calm` of the delete and `deleteJsonReady_of_rowwise`.
- `purge_keeps_rows` and `purge_frame`
  (`tests/surface/Programs/Scripts/PurgeFrameClaims.lean`) take the weaker
  site. The pre of `purge_frame` is `Nonempty (PurgeFrameSite db)`.
- New fixture `tests/surface/Schema/Tests/PurgeFrameSchema.lean`: the
  database `sessions` and `sessionsEntry` (moved from the instances), the
  lookup `sessions_found`, the site `sessionsSite` for each database with
  `db.HasCatalog sessions`, and the frame client statement
  `purge_frame_on_sessions` with the catalog as its only premise.
- `tests/surface/Schema/Tests/PurgeFrameInstances.lean`: the site-for-values
  theorems (`null_customer_has_a_site`, `null_time_has_a_site`,
  `text_time_has_a_site`, with `modeledAtFifty` and `fiftySite`) are replaced
  by uses of `purge_frame_on_sessions` (`null_customer_keeps_the_frame`,
  `null_time_keeps_the_frame`, `text_time_keeps_the_frame`).
  `purge_frame_typed` has the catalog as its pre. The decide checks stay.
- `big_after_delete` in `SelectContextCases.lean` still has a premise
  `modeled` that its DELETE step continues. It does not use the site and is
  outside this task.
- The fields of `sessionsSite`: the position, the entry, the names and the
  two states after the resolution are values of `sessions`. `keyAlias` is
  decided by the kernel. `found` and `claimResolves` rewrite the catalog of
  the database to that of `sessions` with the premise, then the kernel
  decides them. `purgeResolves` rewrites the resolution state of the idle
  connection with `Database.resolveState_of_catalog`, then the kernel
  decides it.
- Tests: `test_purge_frame_claim_over_every_database` compiles the chain
  with `PurgeFrameSchema`; the new module is in the `surface` roots.

Elaboration time of the fixtures (lower of two runs, local):
`PurgeFrameQueries` 1.0 s, `PurgeFrameSite` 1.0 s, `PurgeFrameClaims`
1.3 s, `PurgeFrameSchema` 1.3 s, `PurgeFrameInstances` 3.1 s.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local); `python3 -m pytest tests/test_source_identity_derivations.py`
passed (local).

### The effect claim (fixtures)

- New fixture `tests/surface/Programs/Scripts/PurgeEffectClaims.lean`:
  - `purgeClears`: `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE
    customer_id = $c AND expires_at < $now)`.
  - `purgeClears_iff`: on a database with the catalog of `sessions`, the
    claim holds exactly when the filter is true for no row of the table.
    The proof uses `resolveStatement_selectOne_notExists`, `tableOne_run`
    and `whereOne_claims`, as the task file says.
  - `purge_clears`: the effect client statement, with the catalog as its
    only premise. The proof runs the purge with `sql_run`, with
    `PurgeFrameSite.purge_continues` as the hint for the step. It reads the
    rows that `LiteralData.deleted` keeps and uses
    `Resolved.Expr.Rowwise.evaluate_congr` to move the filter from the
    context of the statement to the two values.
- New fixture `tests/surface/Schema/Tests/PurgeEffectInstances.lean`: a use
  of `purge_clears` on `sessions`, and decide checks that the claim is false
  before the purge and true after it (integer time and text time), true
  before and after for a NULL customer, and false after an aborted purge.
- Tests: `test_purge_frame_claim_over_every_database` compiles the chain
  with `SelectOneWhereSupport`, `PurgeEffectClaims` and
  `PurgeEffectInstances`, timeout 300 s. Both new modules are in the
  `surface` roots.
- Effort, for the findings record: `purge_clears` and `purgeClears_iff` are
  about 45 proof lines. No package code was needed beyond the readiness
  facts.

Elaboration time of the fixtures (lower of two runs, local):
`SelectOneWhereSupport` 1.0 s, `PurgeEffectClaims` 1.2 s,
`PurgeEffectInstances` 1.7 s.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local); `python3 -m pytest tests/test_source_identity_derivations.py`
passed (local).

## Form A

Not started.

## Form B

Not started.

## Form C

Not started.

## Form D

Not started.
