# Status: the expression forms IN, BETWEEN, CASE and || (ADR 0018, slice 2)

Created 2026-10-20. Status: DONE (2026-10-21).
Task file: [task](20261020-expression-forms.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D2.

## Progress

- 2026-10-21: the task file, from native probes and SQLite's code (`sqlite3ExprCodeIN`,
  `sqlite3CodeRhsOfIN`, the parser's rewrite of a one-value list).

- 2026-10-21: "the four forms". Syntax `inList`, `between`, `caseOf` (one operand list and a
  base flag, so resolution walks it as call arguments) and `concatenate`; the frontend maps
  them in `belay/sqlite/syntax_forms.py`. Resolution: an `IN` list is the resolved `inList`
  under the left operand's affinity and collation (one constant value with an explicit
  collation is `x = +c`, as SQLite's parser rewrites it); `BETWEEN` is `x >= a AND x <= b`;
  `CASE` is `iif` of its operands, with `base = when` comparisons (`resolveCase`), since SQLite
  itself codes `iif` as `CASE`; `||` is the scalar function `pipes`. Evaluation of an `IN` list
  reuses `inValue` and softens the faults of the values. Tests: `Resolution/FormExamples.lean`
  (the native probes, one kernel proof), the syntax tests, `conformance/authored_expression_forms.py`
  (9 cases, all agree with kernel proofs), `conformance/expression_form_mutants.py` (four
  mutants, each killed), `conformance/expression_form_evidence.py` (corpus 43).

- 2026-10-21: "the end of the slice". Local verdict: no case leaves AGREE; against slice 1,
  135 cases of v5, 22 of v4 and 21 of v3 newly agree (against `main`: 142, 24 and 21). The
  frontend boundary test refused `x || 1`, which is now modeled; it refuses `x & 1` instead.
  `just test-full` passes. Corpus 43 is recorded with the claims at the end of the ADR. DONE.

## Remaining

- PR A and PR B come at the end of ADR 0018.
