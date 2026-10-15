# USING and NATURAL joins, slice 4b of ADR 0012

Created 2026-10-15. Status: IN PROGRESS.
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 2: Joins
(slice 4)", "Owner decisions", item 1 (2026-10-14). Related: slice 4
([task](20261014-joins.task.md), #120 and #121), which refuses `USING` and `NATURAL`
as the restrictions `join-using` and `natural-join`; slice 4c (`RIGHT` and `FULL`)
follows this slice.

## Pull requests

- **Pull request A (subject):** resolution, output names, examples, proofs,
  restriction registry changes, authored coverage cases, mutants and a corpus writer.
  No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus (version 14) is frozen
  and claimed, and cases that newly agree are added to `mustAgree`.

## Outcome

1. **Forms.** An inner or left join, also `,`, may have `USING (c, …)` instead of
   `ON`, and the operator of an inner or left join may start with `NATURAL`. Both are
   inner and left joins with a generated `ON` condition; the evaluation of joins does
   not change. `RIGHT` and `FULL` joins stay the restriction `right-or-full-join`, also
   with `USING` or `NATURAL`.
2. **Condition.** For each name `c` of `USING`, or each column name of the joined table
   that also names a column of the left input for `NATURAL`, the condition is
   `left.c = right.c` with the comparison rules of `ON` and `WHERE`, including their
   affinity and restrictions. `left.c` is the left-most column named `c` in the left
   input (all earlier sources); names compare without ASCII case. `NATURAL` without a
   common column is a cross join. A repeated name in `USING` is accepted.
3. **Merged columns.** The right column `c` of each such pair is merged:
   - `*` omits it; the left column keeps its place and its name as declared.
   - An unqualified `c` does not see it, so `c` names the left column, also in a left
     join, where the right column is NULL for a padded row. If another source that is
     not merged also has `c`, `c` stays `ambiguous column name: c`.
   - The qualified name `u.c` and `u.*` still read it.
4. **Errors.** SQLite's prepare errors, checked on native 3.51.0:
   - a `USING` name that is not a column of both the left input and the joined table
     (also a rowid name): `cannot join using column c - column not present in both
     tables`, with the name as written;
   - `NATURAL` with `ON` or `USING`: `a NATURAL join may not have an ON or USING
     clause`.
   SQLite reports a missing table of any join first, then these errors in join order,
   then the errors of the result columns and clauses. The restrictions `join-using` and
   `natural-join` leave the registry, its documentation and its examples.
5. **Verification target.** Queries change no state; the execution semantics,
   `statementReady` and `Contract.lean` do not change.
6. **Evidence.** Authored coverage cases agree with native SQLite and have kernel
   proofs; each mutant below changes a verdict; the verdict counts of the claimed
   corpora do not go down.

## Tests

- Lean examples: the resolved form of a `USING` and a `NATURAL` join equals the
  resolved form of the same join with the written `ON` condition; the names of `*`;
  an unqualified merged name; the ambiguity with a third source; the errors and their
  order; `NATURAL` without a common column; `USING` with a left-most column of an
  earlier source.
- A proof that a `USING` or `NATURAL` join resolves to a join of the same kind whose
  condition is the conjunction of the generated equalities, so the join laws of
  `QueryJoinLaws.lean` apply unchanged.
- Authored coverage cases: `USING` with one and two names, in an inner and a left
  join; `NATURAL` inner and left, with one, two and no common columns; `*`, `x.*`,
  qualified and unqualified merged names in result columns, `WHERE`, `GROUP BY` and
  `ORDER BY`; a merged name in a left join for a padded row; three tables with the
  left-most column of an earlier source (`FROM t, u NATURAL JOIN v`); a self-join with
  `USING`; a comparison between an INTEGER and a TEXT column (`'02'` matches `2`); the
  ambiguity with a third source; both prepare errors and their order with
  `no such table`.
- Mutants, each changing the verdict of an authored case: `*` keeps the merged right
  column; an unqualified merged name reads the right column; the condition uses the
  right-most instead of the left-most left column; `NATURAL` without a common column
  gives no rows instead of a cross join; a missing `USING` column is not an error;
  `NATURAL` with `ON` is accepted.
- The restriction registry, example, documentation and mutant link tests after the two
  restrictions leave.

## Key points for the implementer

- **Scope.** `Resolution/Scope.lean` has `Source {name, columns}`; `Scope.matches`
  (unqualified names), `Scope.columns` (`*`) and `Scope.source?` (qualified names and
  `x.*`) read every column. A merged column must be invisible to the first two and
  visible to the third. The writes use `Scope.single` and must keep their behavior.
- **Sources.** `Resolution/Sources.lean` (`resolveTables`, `joinFormIssue`,
  `resolveJoinCondition`) builds the scope and refuses the two forms today; the
  generated condition needs the left input's scope and the joined table's offset. The
  error order of item 4 interacts with `resolveTables`, which reports a missing table
  of every join before the conditions are resolved.
- **Syntax.** `Syntax.Join` already has `usingColumns`, and `NATURAL` is in
  `operator`; the frontend maps both (`belay/sqlite/syntax_sources.py`). The frontend
  should not need to change.
- **Comparisons.** Generate the condition as `Syntax.Expr` qualified names and resolve
  it through `resolveJoinCondition`, or resolve the operands directly: either way the
  affinity and the restrictions of a written `=` must apply. A source name generated
  for a qualified name can collide with nothing, since two sources with the same name
  are a restriction.
- **Kernel and mutant cost.** Keep authored cases to two or three tables with a few
  rows. Measure the mutant suite after adding mutants (slice 4 put the join mutants in
  the write measurement for time).
