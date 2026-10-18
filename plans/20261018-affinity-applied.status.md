# Status: affinity is applied, not refused (ADR 0013, step 4)

Created 2026-10-18. Status: open.
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

## Remaining

- Implementation, measurement over every corpus, full checks, review, CI time, pull
  requests A and B.
