# Expression grouping: task status

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Task: [Expression grouping](20261104-expression-grouping.task.md).
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md).
Source baseline: the end of slice 2 ([status](20261104-group-values.status.md)).

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/QueryAggregates.lean`,
`Resolution/QueryAggregatesArms.lean`, `Resolution/QueryTerms.lean`,
`Resolution/RestrictionText.lean`, `DuplicateKeyGroupTerm.lean`,
`Resolution/GroupAssociation.lean`, `docs/semantic-subset.md`.

## Progress

- 2026-11-04: task specified.
- 2026-11-04: implemented. `resolveGroupTermTraced` resolves every term that is not a name, a
  number or an alias under `COLLATE` as an expression (`resolveGroupExpressionTraced`): an
  aggregate is SQLite's error, a subquery is `group-by-term`, an alias inside the term is
  `alias-in-expression`. `columnNumber` and `Syntax.Expr.withoutCollate` moved to
  `Resolution/QueryTerms.lean` and serve both ORDER BY and GROUP BY. A number under `COLLATE`
  names its column under that collation; an alias under `COLLATE` is the aliased expression
  under it, and `associatedResult` follows D5 for it. Lemmas
  `resolveGroupTerm_expression`, `resolveGroupExpression_operand` and
  `GroupTermResolvesIn.expression`. New corpus `conformance/authored_expression_grouping.py`
  (34 cases), tests `tests/conformance_expression_grouping_test.py` and
  `tests/surface_expression_grouping_test.py` with `tests/surface/ClaimsExpressionGrouping.lean`.
  Task correction: the failing key with kept rows is not a corpus case. The `group-by-term`
  example of `conformance/restriction_examples.py` is now a subquery; the mutants
  `no_aggregate_in_group_by` and `no_group_by_out_of_range` follow the new code. Besides
  `select5:select5-5.11:21`, the case v5 `indexexpr2:indexexpr2-10.1:124` groups by an
  expression; the slice-end verdict gives the verdict of both, and the claims pull request
  promotes each that agrees.
  Tests for the commit: `tests/conformance_expression_grouping_test.py`,
  `tests/surface_expression_grouping_test.py`, `tests/restriction_registry_test.py`,
  `tests/conformance_restriction_examples_test.py`, `tests/restriction_costs_test.py`,
  `tests/mutant_guards_test.py`.
- 2026-11-04: review fixes. A number or an alias under an unknown `COLLATE` name is
  `unknown-collation`, as in any other expression (guards in `Resolution/CollationExamples.lean`);
  `replaceUnderCollate` lists every form; proof sketch of `namesAliasIn_nil`; the
  `alias-in-expression` text names GROUP BY. The mutant `no_aggregate_in_group_by` makes the
  aggregate check a refusal, because a dropped check still gives a prepare error. Tests for the
  commit: `tests/conformance_query_resolution_mutants_test.py`, `tests/mutant_guards_test.py`,
  `tests/restriction_registry_test.py`, `tests/conformance_restriction_examples_test.py`,
  `tests/surface_expression_grouping_test.py`.
- 2026-11-04: `tests/surface/SuccessUniqueEmail.lean` (`refactor:`): with no email column, the
  guide's term `email COLLATE NOCASE` is now SQLite's `no such column` prepare error, not a
  model restriction; the proof follows, and the collated-column case uses
  `resolveGroupTerm_collatedColumn`.
- 2026-11-04: slice-end checks on the top of the stack (with the claims commits): the first
  `just test-full` failed only in `tests/surface_success_test.py`
  (`test_guide_email_success_uses_exact_corrected_precondition`, fixed above); the second run
  passed. `just verdict` passed with no `DISAGREE`: corpora v56 to v58 agree in all cases, and
  `select5:select5-5.11:21` and `indexexpr2:indexexpr2-10.1:124` agree. Mutant test:
  `tests/conformance_query_resolution_mutants_test.py`. Slice 3 is code complete.
