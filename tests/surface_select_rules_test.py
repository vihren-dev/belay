"""ADR 0027 SELECT phase rules: the run observations, their bridges and the acceptance cases."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(180)]


def test_run_observations(runtime_root: Path, tmp_path: Path) -> None:
    """`Run.returnsResult`, `Run.returnsRows` and `Run.returnsError` read rows, a nonempty choice and
    errors, and refuse unmodeled stops, empty choices and several outputs; `Holds`, `Empty` and `Fails`
    keep their earlier truth values (migration witnesses); the successful-result bridge applies to a
    concrete SELECT. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectRunObservations", 9),), timeout=60)


def test_execution_rule(runtime_root: Path, tmp_path: Path) -> None:
    """The execution rule (`Run.send_returnsResult_select`) and its readiness premises
    (`Connection.SelectReady.of_calm`) prove a universal theorem over every database and environment;
    a possible fault blocks success and error claims (`Run.send_unready`, case B05), also where the
    query output alone has an empty result. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectExecutionRules", 3),), timeout=60)


def test_projection_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A01 through the result, filter and projection rules
    (`Query.mem_possibleResults_plain`, `Run.query_returnsResult_calmTable`): the motivating invoices query
    over every database, with generic table and column premises and with `db.HasCatalog invoices`, as a
    `Sql.check` claim, with an empty and a populated witness and the nullable contrast. Every proof has
    only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectProjectionCases", 6),), timeout=60)


def test_filter_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A02 and A03 through the filter and comparison rules (`Resolved.truthy_isNot_null`,
    `Resolved.ordinary_of_truthy`): `IS NOT NULL` gives non-NULL cells with no schema constraint, and
    `amount > :minimum` gives the modeled comparison for every parameter value, over every database with
    generic premises; a CHECK that accepts NULL, a NULL or NaN parameter, the affinity of the column and
    the type of the parameter are the contrasts. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectProjectionCases", 6), ("SelectFilterCases", 3),
                       ("SelectComparisonCases", 5)), timeout=60)


def test_cardinality_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A04 through the result and projection rules (`Query.perm_of_mem_possibleResults_plain`,
    `Run.returnsResult.mono`): a plain projection is a permutation of the stored rows' cells, so it keeps
    their number and duplicates, and a filter bounds the number of rows; a property of each row gives no
    number of rows and no distinct rows. Existence and emptiness (`Query.forall_possibleResults_ne_nil_plain`,
    `Query.forall_possibleResults_eq_nil_plain`): `Holds` and `Empty` of a filter over every database are a
    kept row and no kept row, with an instance of each side. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectProjectionCases", 6), ("SelectCardinalityCases", 5)),
                       timeout=60)
    check_module_chain(runtime_root, tmp_path, (("SelectExistenceCases", 3),), timeout=60)


def test_expression_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A11 through the expression rules (`resolveStatement_select_table`, the value rules of
    `Model/ExprValueRules.lean`): a projection of a column, a parameter, an arithmetic and a CASE expression
    over every database with generic premises, with a witness; an `abs` call that can fail is not calm, has a
    fault, and its query returns neither a result nor an error, although its value rule gives a value.
    Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectProjectionCases", 6), ("SelectExpressionCases", 4)),
                       timeout=60)


def test_outcome_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases B01, B02 and B11 through the prepare-error rule (`Run.query_prepareError`), the
    bridges of `Sql.check` and `Sql.check_stopped`: a query of a missing table returns error code 1 and no
    result for every database without that table, satisfies the matching error post and no other post; a
    read of the clock without a clock satisfies no post; a choice of results satisfies a post only when each
    alternative does, and the raw choice and each alternative keep their own traces. Every proof has only
    logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectOutcomeCases", 6),), timeout=60)


def test_group_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A07 and A10 through the group, aggregate and order rules (`groups_partition`,
    `records_aggregate`, `Query.groupRow_mem`, `Query.exists_sorted_perm_of_mem_possibleResults`): `GROUP BY`
    with a column and with an expression term gives a partition by the key with the count of each group,
    sorted by an output column, and `HAVING count(*) > 1` keeps exactly the groups of more than one row, over
    every database with the catalog of `orders`; collated key equality is not value equality, a grouping key
    that can fail blocks the claim, a NULL condition keeps no group, and a condition on the row of a group is
    a model claim. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectGroupCases", 6),
                       ("SelectHavingCases", 6)), timeout=90)


def test_count_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A08 and the count rule of A09 through the ungrouped rule
    (`records_ungrouped`) and the count evaluation (`Resolved.countRows_eval`,
    `Aggregate.eval_count_of_notNull`): over every database with the catalog of `orders`, `count(*)` without
    `GROUP BY` returns one row with the number of stored rows, also 0 for no row, a grouped query over no row
    returns no row, and `count(customer)` equals `count(*)` for a NOT NULL column; without NOT NULL a NULL
    customer is not counted. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectGroupCases", 6),
                       ("SelectCountCases", 5)), timeout=90)


def test_sum_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A09 for `sum` through the aggregate rules and the overflow rule
    (`Run.query_overflow_calmTable`): over every database whose catalog has a table `ledger` with a column
    `cents`, `SELECT sum(cents) FROM ledger` returns the one row of the sum when the sum does not fail, and
    the `integer overflow` error when it fails; `Fails`, `Holds` and `Empty` follow. Kernel instances check
    an overflow, a fitting sum, no row, a cancellation that comes too late and texts that `sum` reads as
    integers. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectSumCases", 4), ("SelectSumInstances", 3)), timeout=90)


def test_extremum_and_null_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A09 for `min`, `group_concat` and the empty and NULL inputs through the aggregate
    rules (`Resolved.extremum_spec`, `Aggregate.eval_allNull`): over every database with the catalog of
    `orders`, `min(amount)` is NULL exactly for no row and else the least amount of a row, `group_concat`
    joins the customers with commas, the row of a grouped `min` is the deciding row, and over no row or
    only NULL operands `min`, `max`, `sum`, `avg` and `group_concat` are NULL, `total` is 0.0 and
    `count` is 0. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectGroupCases", 6),
                       ("SelectCountCases", 5), ("SelectExtremumCases", 4), ("SelectNullAggregateCases", 3)),
                       timeout=90)


def test_distinct_order_and_window_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A12, A13 and A14 through the distinct, order and window rules
    (`distinctRecords_rules`, `Query.exists_sorted_of_mem_possibleResults`,
    `Query.length_of_mem_possibleResults`): over every database with the catalog of `orders`,
    `SELECT DISTINCT customer` gives each customer once when NOCASE-equal customers are the same values,
    and no described result for `'acme'` and `'ACME'`; a sort by `amount`, no result column, gives the ids
    of all the rows in order; `LIMIT 2 OFFSET 1` gives as many rows as the window takes, with zero, one,
    many and past-end instances, and both tied winners of `LIMIT 1`. Every proof has only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectDistinctCases", 3),
                       ("SelectOrderCases", 4)), timeout=90)


def test_join_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A05 and A06 through the join rules (`joinRows_inner`, `joinRows_left`,
    `joinRows_right`, `joinRows_full`, `joinRows_inner_length_of_unique`), the two-table source rule and
    the calm execution rule: over every database with the catalog of `shop`, an inner join gives each order
    with each matching customer, and as many rows as orders when each order has one match; a left join
    keeps each order, a right join each customer, a full join both, with NULL cells for the missing side.
    The instances show a removed and a multiplied order and a NULL name of a NOT NULL column. Every proof
    has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectOuterJoinCases", 5)), timeout=90)


def test_subquery_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A18 and A19 through the subquery rules (`statement_one`, `subqueryRun_of_faultless`,
    `results_eq_nil_iff_plain`, `results_plain_unordered`, `windowCertain_of_short`) and the faultless
    execution rule: over every database with the catalog of `shop`, a correlated EXISTS keeps exactly the
    customers with a witness order and NOT EXISTS the others; IN and NOT IN read the first column of every
    order; a scalar subquery gives the amount of the one witness, or NULL. The instances show two outer rows
    with different subquery runs, NOT IN over a NULL, and an empty scalar subquery. Every proof has only
    logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectSubquerySupport", 0), ("SelectExistsCases", 5),
                       ("SelectInCases", 4), ("SelectScalarCases", 2)), timeout=120)


def test_compound_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A16 through the compound rules (`Compound.ending_done`, `SelectReady.of_compound`,
    `perm_of_mem_possibleResults_compound`, the membership rules of UNION, INTERSECT and EXCEPT) and the
    compound execution rule: over every database with the catalog of `shop`, UNION ALL of the customer ids
    and the order customer ids keeps the count of each row, and UNION, INTERSECT and EXCEPT give each row
    once with the members of their rules. The instances show a row that UNION ALL keeps twice and UNION
    once. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectCompoundSupport", 4), ("SelectCompoundCases", 4)),
                       timeout=120)


def test_derived_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A17 through the derived source rule (`Query.source_derived`,
    `Query.windowCertain_unwindowed`) and the faultless execution rule: over every database with its
    catalog, a derived table, a common table expression and a view over the big orders return the
    `customer_id` of each big order, through one rule for the inner query. The instances show a derived
    column that is NULL although its source column is NOT NULL, and a derived table with LIMIT 1 and no
    ORDER BY, for which the model describes no result. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectDerivedSupport", 3), ("SelectDerivedCases", 4)),
                       timeout=120)

def test_parameter_window_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A15 through the faultless execution rule with a bound window and the mismatch rule
    (`resolvedStepOutput_select_mismatch`, `Run.query_mismatch`): over every database with the catalog of
    `orders`, LIMIT ? OFFSET ? with integer values gives the window of the sorted rows, and a LIMIT value
    that is no integer gives the error `datatype mismatch` and no result. The instances show text values
    that SQLite reads as integers, an OFFSET that fails after LIMIT 2, and LIMIT 0, which does not read the
    OFFSET. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectOrderCases", 4),
                       ("SelectParameterWindowCases", 4)), timeout=90)
