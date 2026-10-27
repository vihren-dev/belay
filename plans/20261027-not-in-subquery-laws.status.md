# Status: NOT IN and correlated NOT EXISTS query laws

Created 2026-10-27. Status: OPEN (in progress).
Task: [task file](20261027-not-in-subquery-laws.task.md).
Specs: ADR 0017 S4 and S6; the S6 automation task and its part 2 open point
"notBlocked".

## Decisions

- 2026-10-27 (owner): the universal `notBlockedIn ≈ notBlockedEx` claim gets
  general NOT IN / correlated NOT EXISTS query laws in this separate task, not
  a guide change.

## Progress

- 2026-10-27: task specified on the open PR stack (after table rebuild part 2,
  PR #279). The implementation starts after S6 automation part 2 is published,
  because it extends that part's `notBlocked` fixture.
- 2026-10-27: spec reviews `20261027T054201Z-95604a1b` (1 must, 1 should, both fixed in the next commit;
  the resolution of finding 1 was recorded twice by mistake, both as fixed) and `20261027T054328Z-22df9c12`
  (no findings).
- 2026-10-27: commit 1, model laws (new modules only; no change to SQL meaning or predictions):
  `InValueEqualsLaws` (`inMatches`, `equalsValue`, `equalsAny`), `NotInValueLaw` (value law), `NotInIntegerProbe`
  (integer probe: collation does not matter; `comparisonAffinity_comm`), `NotInSubquerySource` and `NotInSubqueryRun`
  (the two subqueries as builders `Query.columnOf` and `Query.matchingKey`, and their runs for any outer row),
  `NotInFilterLaw` (filter law), `NotInRowidAlias` (structural premises), `NotInSubqueryExamples` (kernel examples).

## Deviations and decisions of the implementation

- The value law `inValue_negated_eq_not_equalsAny` is stronger than the task text: it needs no NULL premise, only that
  the `IN` test and the `=` comparison match the same candidates for a non-NULL probe. With a NULL probe or a NULL
  candidate without a match both sides are NULL. The NULL premises appear in the filter-level corollary
  `inValue_negated_eq_not_exists` (`NOT IN` against `NOT EXISTS`), where the difference is NULL against 1.
- The operand `x` of the filter and query laws is a column of the outer row (`.column key`), not an arbitrary
  expression. A column read has no fault, so "`x` evaluates without fault" holds without a premise. Other operand
  forms are not covered by these laws.
- The run laws take no premise on the length of the outer row: a subquery sees the outer row cut or filled with NULL to
  the width `outer` (`Query.outerCells`). The check of faultless evaluation over the empty row is therefore covered.
- No candidate was found where the model's `IN` comparison and the correlated `=` differ for an integer probe and a
  non-NULL candidate (`inMatches_integer_collation_free`: any two collations, one non-TEXT affinity).
