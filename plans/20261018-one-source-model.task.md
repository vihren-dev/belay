# One source model (ADR 0013, step 5)

Created 2026-10-18. Status: open.
Status file: [status](20261018-one-source-model.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D5, amendment 2,
"Order" step 5, owner decisions 2 and 6.

## Pull requests

- **Pull request A (subject):** the model, the docs of the registry and the tests. No
  change under `judge/` or `integrity/`; `Contract.lean` does not change.
- **Pull request B (judge, owner approval):** adds the frozen cases that agree after
  pull request A and were restricted before to `mustAgree`, with the new lock.

## Outcome

1. **One source list.** `Resolved.Query` has `sources`, a list in written order of
   `Resolved.Source` (`table`, `each` with its arguments, and `subquery` without payload)
   with its join kind and optional `ON` condition. `Query.table`, `joins`, `functions`,
   `EachSource` as a separate list and `splitSources` do not exist.
2. **One join.** Evaluation joins the sources in order, one nested loop: a table gives its
   rows in rowid order; `json_each` gives its rows over the row so far (correlated); an
   inner join keeps the rows where `ON` is true; a left join pads a row without a match;
   right and full joins of tables keep the unmatched rows of the right table. The fault of
   a `json_each` source is part of the query's fault (`may`), so the support check needs no
   separate `eachJsonReady`.
3. **Join operators parsed once** into a kind and a `NATURAL` flag, as SQLite's
   `sqlite3JoinType` does: any order of the words, and repeated words.
4. **`USING` and `NATURAL`** give their equalities directly from the positions of the
   merged columns, with the comparison affinity of those columns. No Syntax is generated
   and resolved again.
5. **Restrictions.** `duplicate-source` and `table-after-function` leave the registry.
   `function-join` covers only `json_each` as the right operand of `RIGHT` or `FULL`, or
   with `USING` or `NATURAL`; `LEFT JOIN json_each` is modeled. `later-table-in-on`,
   `later-source-in-arguments` and `function-join` move to the *unsupported* registry with
   their reasons (amendment 2). No restriction kind `subquery` is added: the frontend
   refuses subqueries before resolution (owner decision 7).
6. **Scope.** Each source of the scope keeps its offset in the joined row; no fold
   recomputes it.

## Tests

- Before the commits that change verdicts: the classifier over every frozen corpus with
  the change; no case is `DISAGREE` or `HARNESS_ERROR`, and every case that agrees today
  still agrees.
- `just test-full`, `just test-nix` and `just test-scheduled` pass; the scheduled mutant
  suite kills every mutant, with anchors moved.
- `#guard` examples, checked natively: `FROM x3, x3` with `count(*)` and the ambiguous
  names; `OUTER LEFT JOIN`; `json_each` before a table; `t LEFT JOIN json_each(t.b)`; the
  pinned `USING` and `NATURAL` conditions of `UsingExamples.lean` and
  `MergedNameExamples.lean` with the same affinities.

## Key points

- **Regression risk.** About 140 cases with joins, 49 with `USING` and 29 with
  `json_each` agree today. Measure each verdict-changing commit over every corpus.
- **Fault rule.** `Query.mayFail` treats a query with joins or `json_each` sources as
  syntactic for JSON calls; keep that rule for a query with more than one source or any
  `json_each` source.
- **Error order.** `USING` and `NATURAL` name errors arise before the result columns; `ON`
  conditions resolve after `WHERE`, and `json_each` arguments after them. Keep which
  prepare error wins (`UsingExamples.lean`).
- **NATURAL** skips hidden columns on both sides; `USING` sees them. With `function-join`
  for `json_each` and `USING` or `NATURAL`, no hidden column reaches them.
- **Names.** `Belay.Sqlite.Source` (the scope record) collides with `Resolved.Source`; rename
  the scope record.
- **Paths.** Restriction paths `[1]` and `[2, item, k]` map to source ranges in the
  frontend; keep them for the Syntax, which does not change.
- **Mutants.** The anchors of `join_mutants`, `right_mutants`, `using_mutants`,
  `merged_mutants`, `json_each_mutants` and `fromless_mutants` move with the code.
