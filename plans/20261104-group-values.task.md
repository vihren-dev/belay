# The values of a group

Date: 2026-11-04. Status: DONE.
Audience: the implementation team.
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md),
slice 2 (D5, the slice-2 parts of D8). Accepted by the owner on 2026-11-04.
Record: [status](20261104-group-values.status.md).
Source baseline: the end of slice 1 ([task](20261104-conditional-creation.task.md)).

This is core work: it changes the values that the model gives for the non-aggregate expressions
of an aggregate query. It changes predictions, so it adds a corpus and its claim; those go into
the claims pull request at the end of the ADR (D8).

## Required behavior

When the task is done, all of these are true for every aggregate query that the model resolves
today (this slice adds no new grouping terms):

1. **Deciding call.** The deciding call of a query is the last distinct `min` or `max` call in
   the order: result columns, then `ORDER BY`, then `HAVING`; a call that is written again counts
   at its first place. A query without such a call has none.
2. **The row of a group.** Without a deciding call, it is the first row of the group in the
   order of the source (as today). With a deciding call, it is the first row in that order whose
   operand value is the call's result under the call's collation; when the operand is NULL on
   every row of the group, it is the last row of the group.
3. **Association.** For each grouping term, at most one result column is associated with it: a
   number names its result column; every other term (also an alias, as its aliased expression)
   is associated with the last result column whose written form is the same expression. Two
   written expressions are the same when they are the same tree with every column reference
   resolved to its source column, function and collation names compared without case, `CAST`
   type names compared with case, and the same `COLLATE` and unary plus nodes at the same
   places.
4. **Values.** An associated result column whose written form is not a column under at most
   `COLLATE` gives the term's value on the first row of the group. Every other result column,
   every `HAVING` condition and every `ORDER BY` expression reads its column references from the
   row of the group (item 2), also when it is equal to a grouping term.
5. **One result everywhere.** `Query.results`, `possibleResults`, subqueries, derived tables,
   compound terms and `INSERT ... SELECT` read this one result. A query without `min` or `max`
   and without an associated non-column result gives the same result as before.
6. **Proofs.** Every theorem that reads the values of a group keeps its statement, with the row
   of item 2. Every new proposition has its plain-words docstring.
7. **Documentation.** `docs/semantic-subset.md` documents the row of a group and the
   association, in the commit that changes the behavior.

## Tests

- **Authored corpus**, recorded with the native oracle (version 7 records): the rows of "What
  the model gives today" of the ADR except the index-dependent query; `min` and `max` in both
  orders and across the result, `ORDER BY` and `HAVING`; a repeated call; a tie of the maximum
  whose rows differ; a result column written twice and grouped by number and by alias;
  `COLLATE` and unary plus on one side only; `CAST` type names that differ in case, compared
  through an alias; a deciding call whose operand is NULL on every row of a group. A probe whose
  term is a written expression (`GROUP BY a+0`) needs slice 3 and goes into its corpus. Every case
  agrees, and the corpus is claimed in the claims pull request with all its cases in
  `mustAgree`.
- **Claimed corpora**: no verdict of a claimed case changes from `AGREE`. A case that changes
  for the reason of D5 (the plan of SQLite) is an owner decision before the pull request.
- **Kernel-checked surface example** in `tests/surface`: the row of a group for a query with
  `max`, with `min` then `max`, and with an associated expression column, on a small database.

## Implementation notes

- `records` (`QueryResults.lean`) evaluates the expressions of a group on `group.headD []`; the
  theorems of `DuplicateKeyQuery.lean` state results with `group.headD []`. With no `min` or
  `max` those statements stay true; check which laws assume a deciding call cannot exist.
- The resolver collects `Query.aggregates` in another order (calls inside result expressions,
  then `HAVING`, then `ORDER BY`, and without result columns that are an aggregate themselves:
  `resolveQueryBodyTraced`, `QueryBodyTraced.lean`). The deciding call needs the written order
  of the item 1 list, so the resolver records it, or the query records its own order.
- The association compares written expressions (`Syntax.Expr`), because the resolved form keeps
  no `COLLATE` node. Column references must still compare as resolved columns, so `a` and
  `t.a` are the same column.
- The translation refuses `FILTER` on every call (`Translation/Queries.lean`), so the ADR's
  `FILTER` rule has no case in this slice. The model needs no code for it.
- `Resolved.Expr.grouped` and the restriction `bare-column` do not change; a result column
  that is a grouping column is evaluated on the row of the group.
- Before writing per-law cases, analyse the most general form (owner rule): one definition of
  the row of a group, and laws in terms of it.
