# RIGHT and FULL joins, slice 4c of ADR 0012

Created 2026-10-15. Status: IN PROGRESS.
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 3: RIGHT and
FULL joins (slices 4c and 4d)", "Rows (slice 4c)", with the owner decisions of
2026-10-15 (#124). Related: slice 4 ([task](20261014-joins.task.md)) and slice 4b
([task](20261015-using-natural.task.md)); slice 4d (USING and NATURAL with right and
full joins) follows this slice.

## Pull requests

- **Pull request A (subject):** resolution, evaluation, proofs, restriction registry
  changes, examples, authored coverage cases, mutants and a corpus writer. No change
  under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus (version 15) is frozen
  and claimed, and cases that newly agree are added to `mustAgree`.

## Outcome

1. **Forms.** `RIGHT [OUTER] JOIN` and `FULL [OUTER] JOIN`, with an `ON` condition or
   without one, run in any position of the join list. The restriction
   `right-or-full-join` leaves the registry, its documentation and its examples.
2. **Rows.** A right join is the inner join of its left input (all earlier sources) and
   the joined table, plus each row of the joined table that no row of the left input
   matches, with NULL in every column of the left input. A full join adds both the
   unmatched left rows (as a left join) and the unmatched right rows. An empty left
   input makes every right row unmatched. `WHERE`, groups, aggregates, projection,
   `ORDER BY` and the window then work on the joined rows as before.
3. **Order.** The inner part (with the padded left rows of a full join) in the order of
   slice 4, then the unmatched right rows in rowid order. Rows are compared as multisets
   where the order is not observable (ADR 0005).
4. **Names.** Qualified and unqualified names, `*` and `x.*` as for inner and left
   joins; a qualified column of a padded table is NULL.
5. **Restrictions.** `USING` or `NATURAL` anywhere in a `FROM` that has a right or full
   join is a new model restriction until slice 4d, with an id, message, documentation
   row and example. An `ON` condition that names a later table stays
   `later-table-in-on`.
6. **Verification target.** Queries change no state; the execution semantics,
   `statementReady` and `Contract.lean` do not change.
7. **Evidence.** Authored coverage cases agree with native SQLite and have kernel
   proofs; each mutant below changes a verdict; the verdict counts of the claimed
   corpora do not go down.

## Tests

- Lean examples: the resolved kinds; the rows of a right and a full join over small
  tables, also with an empty left or right table and with `ON` false for every row; a
  right join after an inner and a left join; the new restriction, also for `USING`
  before a later right join.
- Proofs: a joined row of a right or full join has the width of its tables; a full join
  keeps every left row as a prefix and every right row as a suffix of some joined row; a
  right join keeps every right row as a suffix; the existing laws of
  `QueryJoinLaws.lean` keep holding for inner and left joins.
- Authored coverage cases, as Amendment 3 "Testing" lists for slice 4c, plus an empty
  left table; the frontend keywords in mixed case.
- Mutants, each changing the verdict of an authored case: a right join drops
  unmatched right rows; a right join pads the right row's own columns instead of the
  left input's; an unmatched right row is decided per left row instead of over the
  whole left input; a full join omits the unmatched left rows.
- The restriction registry, example, documentation and mutant link tests after the
  restriction changes.

## Key points for the implementer

- **Width of the left input.** `QueryEval.joinRow` pads a left row with the joined
  table's width. A right join pads a right row with the width of the left input, which
  the rows cannot give when there are none; `Query.source` knows the tables, so the
  width must come from them.
- **Matching over the whole left input.** An unmatched right row is one that no left
  row matches, so the evaluation cannot stay a `flatMap` over left rows alone
  (`QueryEval.joinRows`). Keep the inner and left paths, and their laws in
  `QueryJoinLaws.lean`, as they are where possible.
- **Module size.** `QueryEval.lean` has 192 lines; the join evaluation should move to its
  own module.
- **Resolution.** `Resolved.JoinKind` (`Resolution/QueryForm.lean`) has `inner` and
  `left`; `Syntax.Join.resolvedKind` and `joinFormIssue` (`Resolution/Sources.lean`) map
  and refuse the right and full operators today; `mergeJoins` and `mergeJoin`
  (`Resolution/JoinUsing.lean`) handle `USING` and `NATURAL`, which must now be refused
  when any join of the list is right or full, also a join before it.
- **Kernel and mutant cost.** Keep authored cases to two or three tables with a few
  rows. Measure the mutant and model suites after the change.
