# Status: affinity is applied, not refused (ADR 0013, step 4)

Created 2026-10-18. Status: DONE.
Task file: [task](20261018-affinity-applied.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D4.

## Relevant files

- Resolution: `packages/belay-sqlite/Belay/Sqlite/Resolution/QueryAffinity.lean`,
  `QueryExprs.lean`, `ExprForms.lean`, `QueryForm.lean`, `Restrictions.lean`,
  `RestrictionText.lean`, `OperandIssues.lean`, `IssueLemmas.lean`.
- Evaluation: `Comparison.lean`, `ExprEval.lean` (`truthy`), `StoreValue.lean`
  (`numericText`), `Arithmetic.lean` (`Value.toReal`).
- Docs and tests: `docs/semantic-subset.md` (restriction registry),
  `conformance/restriction_examples.py`, `tests/restriction_registry_test.py`,
  `tests/cli_refusal_test.py`.
- Claims: `judge/claims.json`, `integrity/judge.lock.json`.

## Progress

- 2026-10-18: code map done. 60 verdict entries are restricted by the four kinds
  (corpus v3: 2, v4: 8, v5: 50; value-as-condition 54, text-to-number 3,
  mixed-affinity-comparison 3).

- 2026-10-18: measured over every frozen corpus before the commit: 58 restricted
  entries agree (v3: 2, v4: 7, v5: 49), `e_select-0.2.0011.1` (v4, v5) meets
  `bare-column` instead, and no case disagrees. The comparison stores its affinity, so
  `+x` needs no node (ADR implementation notes). The registries are
  `RestrictionKind.registry` (`Resolution/RestrictionRegistry.lean`); the docs table has
  a part for each. `tests/cli_refusal_test.py` uses `rowid-name` as its expression
  example. Reviews: one "should" (a file over 200 lines), fixed by moving the truth-test
  examples to `TruthTestExamples.lean`; the other reviews are clean. The three suites
  pass. CI time against step 3: `tests.harness` 22 s to 22 s, `tests.model` 332 s to
  334 s, `tests.frozen` 140 s to 141 s, scheduled mutants 412 s to 411 s.

- 2026-10-18: pull request A is #162. Pull request B adds the 58 newly agreeing
  entries to `mustAgree` (corpus v3: 64, v4: 309, v5: 975 cases); the judge lock
  changes only in its judge entry.

## Remaining

- None. Step 5 of ADR 0013 follows.
