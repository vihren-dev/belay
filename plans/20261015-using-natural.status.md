# Status: USING and NATURAL joins (slice 4b)

Created 2026-10-15. Status: DONE.
Task: [task](20261015-using-natural.task.md).
Specification: [ADR 0012, Amendment 2, "Owner decisions", item 1](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Scope.lean`,
`Resolution/Sources.lean`, `Resolution/Queries.lean`, `Resolution/QueryExprs.lean`,
`Resolution/Restrictions.lean`, `Resolution/RestrictionText.lean`,
`Resolution/JoinExamples.lean`, `QueryJoinLaws.lean`, `conformance/authored_joins.py`,
`conformance/restriction_examples.py`, `docs/semantic-subset.md`.

## Progress

- 2026-10-15: task and status files created. Native 3.51.0 checked for the task's
  rules: the merged columns in `*`, `x.*` and unqualified names; the left-most left
  column (`FROM t, u NATURAL JOIN v`); the comparison affinity (`'02'` matches `2`);
  `NATURAL` without a common column; a repeated `USING` name; both prepare errors and
  their order after `no such table`.
- 2026-10-15: the model: `Source.merged` hides merged columns from `*`
  (`Scope.visible`) and unqualified names; `Resolution/JoinUsing.lean` generates the
  condition as qualified syntax, so a written `ON` and `USING` resolve the same, with
  three proofs (`mergeJoin_written`, `mergeJoin_using`, `mergeJoin_natural`);
  `resolveTables` resolves every table before the join forms; the errors
  `joinUsingColumn` and `naturalJoinCondition`; `join-using` and `natural-join` leave the
  registry. Lean examples in `Resolution/UsingExamples.lean`. The INTEGER and TEXT case
  moved from the native cases to a Lean example: the comparison is the restriction
  `mixed-affinity-comparison`, as for a written `ON`, so no native case can agree.
- 2026-10-15: review of the model commit (1 must, 1 should, fixed): a proof sketch for
  `usingNames_checked`; explicit statement cases in `UsingExamples.queryOver`.
- 2026-10-15: 22 authored cases (`conformance/authored_using.py`, all AGREE), six
  mutants (`conformance/using_mutants.py`, in the write and join measurement), and the
  corpus 14 writer.
- 2026-10-15: CI time (local, `--check` rebuilds, main vs branch): harness 21/22 s,
  mutants 143/157 s, model 192/212 s, frozen 136/136 s. The coverage and round-trip
  tests recorded each authored case set natively twice; a module fixture now records it
  once (11 s for the 8 sets), and the model suite takes 198 s.
- 2026-10-15: pull request A merged as #122.
- 2026-10-15: pull request B: corpus 14 (22 cases) is claimed, and the cases that agree
  since #122 join `mustAgree`: 3 in v3 and 7 in v5, all `e_select`. New judge lock.
  Slice 4b is DONE; slice 4c (RIGHT and FULL joins) follows.
