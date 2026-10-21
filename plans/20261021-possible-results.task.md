# The results that SQLite may give (ADR 0018, slice 6)

Created 2026-10-21. Status: open.
Status file: [status](20261021-possible-results.status.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D6; ADR 0017, D3 and D5
(`Output.oneOf`); the target user guide, section "Row order".

## Process

As for slices 1 to 5: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **The list of results.** For a query over its source rows, the model gives the list of every
   result that SQLite may give. The records are those of `Query.uniqueRecords`, in the stable
   order of the `ORDER BY` terms. They form tie groups: the longest runs of records that the
   `ORDER BY` terms do not separate (`compareSort` gives `eq`); a query without `ORDER BY` has
   one group of all its records. Each result is the rows of the window, group by group, in the
   order of the groups, and the rows of each group in normal form: sorted by
   `compareValues`, column by column. A group that the window holds whole gives all its rows; a
   group that `OFFSET` or `LIMIT` cuts gives, in each result, one of the ways to choose as many
   of its rows as the window takes from it. The list has each result once.
2. **One result when the window cuts no tie.** A query without `LIMIT` and `OFFSET`, or whose
   window cuts no group, has one result. Its rows are those of `Query.results` with each group
   in normal form, so a query without `ORDER BY` gives its rows sorted, as the guide's normal
   form says. When every way to choose gives the same rows, as for `SELECT 1 FROM t LIMIT 1`,
   the list has one result too.
3. **A statement's query.** The list is available for a query of a statement over a database
   at a clock value, as `Query.runOn` gives its one result, for the surface's `Output.oneOf`
   (ADR 0017, D3).
4. **Laws.** Kernel-checked theorems relate the list to the one result that the model computes
   (`Query.results`): the list is never empty; each of its results has as many rows as
   `Query.results`; and `Query.results` with the rows of each of its groups in normal form is in
   the list. So the corpora, which check `Query.results` against SQLite, check one element of
   the list.
5. **The corpora check the list.** The comparison of a query's output also requires that the
   rows that SQLite gave, with the rows of each tie group of the native evidence in normal form,
   are in the model's list. The comparison changes no verdict that agrees today unless the list
   is wrong.

## Tests

- Lean examples of each outcome with kernel proofs: the guide's three cases (`SELECT name FROM
  customers` gives one sorted result, `ORDER BY` with ties, `LIMIT 1` without `ORDER BY` over
  two rows gives two results), `SELECT 1 ... LIMIT 1` with one result, a window cut by `OFFSET`
  and `LIMIT` in one group and in two groups, the guide's pagination with eleven equal
  priorities (two pages that may share a row), `DISTINCT` and `GROUP BY` with `LIMIT`.
- The laws of outcome 4 as theorems over every query and rows.
- An authored corpus (`conformance/authored_possible_results.py`), each case with a kernel
  proof, recorded as corpus 47: `LIMIT` and `OFFSET` that cut ties of `ORDER BY`, also with
  `DESC` and a collation; `LIMIT` without `ORDER BY` over a table with an index that changes
  SQLite's order; `DISTINCT`, `GROUP BY` and an aggregate query with `LIMIT`; a window that cuts
  no tie; `LIMIT 0`.
- The verdict of every corpus: no case leaves AGREE.
- Mutants: a list that ignores `OFFSET`, a list with only the choice of `Query.results`, a
  list that cuts a group with one row too many, and groups that `DESC` does not reverse; each
  killed by an authored case.

## Key points

- **The tie groups are SQLite's.** The recorder's groups (`conformance/native_ordering.py`)
  rank the rows by the `ORDER BY` terms with SQLite's own comparison, and give, for each group
  that the window reaches, its full rows and the number that the window takes. The model's
  groups must be the same runs, so they use `compareSort`, the comparison of `ORDER BY`.
- **The number of results grows as the binomial coefficient** of a cut group's size and count,
  at most for two groups (the first and the last of the window). The corpora's queries are
  small; the kernel evaluates the list in the proofs, so the choices must be computed by
  structural recursion, as `stableSort` is.
- **`Query.results` takes the first rows of a cut group in record order**, which is the scan
  order of the source. The law places that choice in the list; the mutant with only that
  choice needs a case where SQLite takes other rows, such as an index that changes its order.
- **The comparison is subject code.** The new check is in `VerifierConformance` (`Case.lean`,
  `Outputs.lean`), which the predictions run; it changes neither the judge nor its claims.
- **Files.** `QueryResults.lean` (or a new module beside it), `Subqueries.lean` (`runOn`),
  `VerifierConformance/Outputs.lean` and `Case.lean`.
