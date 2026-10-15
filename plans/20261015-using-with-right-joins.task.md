# USING and NATURAL with RIGHT and FULL joins, slice 4d of ADR 0012

Created 2026-10-15. Status: IN PROGRESS.
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 3: RIGHT and
FULL joins (slices 4c and 4d)", "Names with USING and NATURAL (slice 4d)" (#124).
Related: slice 4b ([task](20261015-using-natural.task.md)) and slice 4c
([task](20261015-right-full-joins.task.md)), which refuses `USING` and `NATURAL` in a
`FROM` with a right or full join as the restriction `using-with-right-join`.

## Pull requests

- **Pull request A (subject):** resolution, examples, proofs, restriction registry
  changes, authored coverage cases, mutants and a corpus writer. No change under
  `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus (version 16) is frozen
  and claimed, and cases that newly agree are added to `mustAgree`.

## Outcome

1. **Forms.** `USING` and `NATURAL` run in every join of a `FROM` that has a right or
   full join. The restriction `using-with-right-join` leaves the registry, its
   documentation and its examples.
2. **Unqualified merged names.** SQLite resolves an unqualified name over the sources
   from left to right (checked on native 3.51.0). The first source with the name gives
   its column. A later source with the name changes the result only when its own join
   merges the name:
   - an inner or left join keeps the current result;
   - a right join replaces it with its own column, with that column's value and
     affinity;
   - a full join extends it to `coalesce(current, its column)`, which has no affinity;
   - a later source that has the name but does not merge it makes the name
     `ambiguous column name`.
   Without right and full joins this is the rule of slice 4b. Examples:
   `t RIGHT JOIN r USING (a)` with `r.a` REAL gives `1.0`; `t FULL JOIN u USING (a)
   FULL JOIN w USING (a)` gives `coalesce(t.a, u.a, w.a)`; `t RIGHT JOIN u USING (a)
   FULL JOIN w USING (a)` gives `coalesce(u.a, w.a)`.
3. **`*`.** The merged column of `*` is the unqualified name of item 2, at the place of
   the left-most column and named by its name as declared; `x.*` and qualified names
   still read each table's own column.
4. **Generated condition.** When the `FROM` has a right or full join anywhere, the left
   side of each generated equality of every `USING` and `NATURAL` join, also one before
   the right join, is the left column if exactly one left table has the name, and
   otherwise the coalesce of all of them in order. Every such table after the first
   must merge the name by its own `USING` or `NATURAL`; else the query is SQLite's
   prepare error `ambiguous reference to a in USING()`, with the name as written.
   Without right and full joins the left side stays the left-most column (slice 4b).
5. **Errors.** The prepare errors of slice 4b apply unchanged, in the same order; the
   new error comes in join order with them.
6. **Verification target.** Queries change no state; the execution semantics,
   `statementReady` and `Contract.lean` do not change.
7. **Evidence.** Authored coverage cases agree with native SQLite and have kernel
   proofs; each mutant below changes a verdict; the verdict counts of the claimed
   corpora do not go down.

## Tests

- Lean examples: the resolved operand of an unqualified merged name for each kind of
  join and for chains of two merges (right then full, full then right, full then inner,
  left then full); `*` of a right and a full join; the coalesced left side of a later
  `USING`; the new error, also for a join before the right join and for `NATURAL`; the
  rule of slice 4b without right joins.
- A proof that, for a `FROM` without right and full joins, the resolution of names and
  of the generated conditions is the one of slice 4b, so the slice 4b examples and
  laws keep holding.
- Authored coverage cases: the examples of Amendment 3 "Context" and of item 2 above;
  a REAL right column (`1.0`) against an INTEGER left column; the coalesce and its
  missing affinity in `WHERE`; `*`, `x.*`, qualified names, `GROUP BY` and `ORDER BY` of
  a merged name; `NATURAL RIGHT JOIN` and `NATURAL FULL JOIN`; the new error in each
  form; the slice 4b errors with a right join.
- Mutants, each changing the verdict of an authored case: a right join's merged name
  uses the left column; a full join's merged name uses the left column instead of the
  coalesce; the coalesce keeps the left column's affinity; the generated condition of a
  later `USING` uses the left-most column instead of the coalesce; a left table that
  does not merge the name is accepted instead of `ambiguous reference to a in USING()`.
- The restriction registry, example, documentation and mutant link tests after the
  restriction leaves.

## Key points for the implementer

- **Scope.** `Source.merged` (`Resolution/Scope.lean`) hides a merged column from
  `Scope.matches` and `Scope.visible`. The new rule needs, for each source, which names
  its join merged and the kind of that join; the result of an unqualified name can be
  an expression (`Resolved.Expr.coalesce`), not only one position.
- **Operands.** `resolveOperand` (`Resolution/QueryExprs.lean`, 196 lines) turns
  `Scope.matches` into an operand with an affinity; `COALESCE` already resolves to
  `Resolved.Expr.coalesce` with no affinity. `definedName` (`Resolution/Returning.lean`)
  names result columns. `GROUP BY` terms in `Resolution/Queries.lean` match identifiers
  through `Scope.matches` directly.
- **Generated condition.** `mergedCondition` and `Scope.leftMost`
  (`Resolution/JoinUsing.lean`) build `left.c = right.c` as qualified syntax; the
  coalesced left side can be built as a `COALESCE` call (`Syntax.Expr.callPair`) of
  qualified names, so it resolves with the rules of a written one. The theorems
  `mergeJoin_using` and `mergeJoin_natural` state the slice 4b condition and must keep
  holding, or be restated, for a `FROM` without right joins.
- **Module size.** `QueryExprs.lean` is near the limit; put the merged-name resolution
  in its own module.
- **Kernel and mutant cost.** Keep authored cases to two or three tables with a few
  rows; measure the mutant and model suites after the change.
