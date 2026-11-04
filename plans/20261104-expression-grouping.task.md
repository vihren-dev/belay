# Expression grouping

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md),
slice 3 (D4, D6, the second and third items of D7, the slice-3 parts of D8).
Record: [status](20261104-expression-grouping.status.md).
Source baseline: the end of slice 2 ([task](20261104-group-values.task.md)).

This is core work: it lets a `GROUP BY` term be an expression, which changes predictions. It
adds a corpus and its claim, and promotes one case; those go into the claims pull request at
the end of the ADR (D8).

## Required behavior

When the task is done, all of these are true:

1. **Identifier.** A `GROUP BY` identifier is a column of the scope, else a result alias, as
   before.
2. **Number.** An integer literal, also under parentheses or unary plus, names a result column.
   `0`, a negative integer and a number past the last result column are SQLite's
   `%s GROUP BY term out of range - should be between 1 and %d`. Any other literal (`1.0`,
   `'1'`) is a constant expression: one group.
3. **Alias inside an expression.** A result alias inside a larger term (`GROUP BY k+1`) is the
   restriction `alias-in-expression`.
4. **Every other term** resolves as a `WHERE` operand of the query's scope does, with the same
   restrictions. An aggregate anywhere in the term is SQLite's
   `aggregate functions are not allowed in the GROUP BY clause`. A subquery in the term is the
   restriction `group-by-term`, whose text becomes "a subquery is not modeled in GROUP BY". The
   counter functions and random values stay restricted in `GROUP BY` (ADR 0024).
   A number under `COLLATE` names its result column with the explicit collation, and is
   associated with it; an alias under `COLLATE` is the aliased expression under the same
   `COLLATE` clauses, associated with the last result column that is the same expression,
   `COLLATE` included (ADR 0030, D4 note of 2026-11-04).
5. **Collation.** The term's collation is an explicit `COLLATE`, else the column's collation
   through unary plus and `CAST`, else `BINARY`.
6. **Grouped expressions.** `Resolved.Expr.grouped` admits a result expression that is a
   grouping term or is made of grouping terms, values and aggregates; a column outside them is
   still `bare-column`. `SELECT lower(a) || '!' ... GROUP BY lower(a)` resolves, and
   `SELECT a ... GROUP BY lower(a)` is `bare-column`.
7. **The values of a group.** D5 (slice 2) applies to expression terms: a result column that is
   the same written expression as a term is associated with it.
8. **Proofs.** `GroupTermResolves` covers an expression term: the resolved term of a written
   expression is its resolved operand. The duplicate-key laws hold for such keys with their
   existing premises. The resolution arms follow the new case split. Every new proposition has
   its plain-words docstring.
9. **Documentation.** `docs/semantic-subset.md` documents expression terms in `GROUP BY`, and
   its restriction table gives the new text of `group-by-term`, in the commit that changes the
   behavior.

## Tests

- **Authored corpus** `expression-grouping-*`, recorded with the native oracle (version 7
  records), with the probes of "Grouping: SQLite" of the ADR: storage classes and `+0`, NULL
  keys, the collation cases, aliases and alias shadowing, the numbers `(1)`, `+1`, `-1`, `0`,
  `1.0`, `'1'`, a number and an alias under `COLLATE`, aggregate terms, a failing key
  without kept rows, rule 3 of the row of a group with a single `max`, a result column written twice and grouped by
  expression, and a `date(x, 'unixepoch')` key with an explicit clock. Every case agrees; the
  claims pull request claims the corpus with all its cases in `mustAgree`. A form that the
  model refuses (an alias inside a term, a window term, a bare column, a subquery term) cannot
  agree, so it is not a corpus case; a checked example in the model gives its restriction or
  translation refusal. Correction (2026-11-04): the list named a failing key with kept rows too.
  The model says only that such a key may fail (ADR 0030, D4), so its outcome is
  `MODEL_UNSUPPORTED` and cannot agree; the corpus has the failing key without kept rows only.
- **Promotion.** v5 `select5:select5-5.11:21` agrees and goes into `mustAgree`.
- **Retained.** v5 `select8:select8-1.*` (`bare-column`), an alias inside a grouping term, v55
  `insert-query-group-by`, and the authored aggregate-in-`GROUP BY` and out-of-range cases of
  `conformance/authored_queries.py` keep their verdicts. No other claimed verdict changes.
- **Registry and messages.** `tests/restriction_registry_test.py` and the restriction text
  tests pass with the new text of `group-by-term`.
- **Kernel-checked surface example** in `tests/surface`: a grouped expression's result on a
  small database.

## Implementation notes

- `resolveGroupTermTraced` (`Resolution/QueryAggregates.lean`) is the case split. Its
  identifier arm resolves the scope first and the alias second; keep that order. `namedResult`
  and `integerLiteral` (`Resolution/QueryTerms.lean`) decide which terms are numbers; check how
  the translation gives `(1)` and `+1`.
- `HAVING` and `ORDER BY` refuse a result alias inside an expression with `namesAlias`
  (`Resolution/QueryBodyTraced.lean`). `GROUP BY` sees all aliases, not only the visible ones.
- `resolveOperandTraced` resolves `WHERE` operands. An aggregate in a `GROUP BY` term must give
  SQLite's error, not the restriction `aggregate-in-expression`.
- Today a call of one or no argument that is not an aggregate goes to `callIssue`, so
  `GROUP BY LOWER(a)` is `unmodeled-function`. The new rule resolves it as an operand.
- `Resolved.Expr.grouped` (`Resolution/QueryTerms.lean`) compares resolved expressions
  structurally; check that an expression key and the same result expression resolve to equal
  forms, also when names differ in case.
- `GroupAssociation.lean` (slice 2) already associates a written expression term with the last
  same result column; with expression terms that path becomes reachable.
- `GroupTermResolves` and its arms are in `DuplicateKeyGroupTerm.lean` and
  `Resolution/QueryAggregatesArms.lean`. Before writing per-form lemmas, analyse the most
  general form (owner rule): one lemma for a term that resolves as an operand.
- A `date` key reads the clock (`DateFunction.readsNow`, `ClockReads.lean`): the corpus case
  needs an explicit clock in its record.
