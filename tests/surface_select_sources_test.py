"""ADR 0027 SELECT phase rules of sources and contexts: joins, subqueries, compounds, derived and
table-free sources, and window parameters, through their acceptance cases."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(180)]


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


def test_source_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A20 through the source rules of a query without a table (`Query.source_none`,
    `Query.source_pragma`, `Query.source_each`, `Query.source_each_fault`): over every database,
    `SELECT 1 + 2` returns the one row 3; over every database with the catalog of `shop`, a pragma source
    returns the column names, and `json_each(?)` returns the value cell of each JSON row of the bound
    value; a malformed JSON argument gives no result and no error, because its fault stays. The instances
    show `count(*)` without FROM, which counts the one row with no cells. Every proof has only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectDerivedSupport", 3), ("SelectSourceCases", 4)),
                       timeout=120)


def test_parameter_window_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance case A15 through the faultless execution rule with a bound window and the mismatch rule
    (`resolvedStepOutput_select_mismatch`, `Run.query_mismatch`): over every database with the catalog of
    `orders`, LIMIT ? OFFSET ? with integer values gives the window of the sorted rows, and a LIMIT value
    that is no integer gives the error `datatype mismatch` and no result. The instances show text values
    that SQLite reads as integers, an OFFSET that fails after LIMIT 2, and LIMIT 0, which does not read the
    OFFSET; the contrasts show that a negative LIMIT or OFFSET has no bound, and that a negative LIMIT reads
    a NULL or missing OFFSET and fails, also with `WHERE 0`. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectOrderCases", 4),
                       ("SelectParameterWindowCases", 4)), timeout=90)


def test_context_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Acceptance cases A21 and A22 through the context rules of a SELECT (`check_query_select_at`,
    `check_query_select_faultless`) and the delete rule (`Sql.check_send_plainDelete`,
    `Connection.resolveState_afterWrite`): at every context with the catalog of `shop`, the big-orders
    query returns the rows of the database of that context; after any program, `sql_select` proves the same
    read at each reached context through `Sql.check_query_ofResolveState` and the leaf's `assumption`, also
    after a delete; at every context whose
    counters know `changes()`, `SELECT changes()` returns that value and keeps the connection. The
    instances show a result from the start that does not hold after a delete, and `changes()`, which has
    no result in the default environment but the count of the delete after it. Every proof has only
    logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectGroupSupport", 0), ("SelectJoinSupport", 0),
                       ("SelectJoinCases", 3), ("SelectDerivedSupport", 3), ("SelectContextCases", 4)),
                       timeout=120)


def test_function_fault_cases(runtime_root: Path, tmp_path: Path) -> None:
    """Cases B01 and B05 without a table through the must-fail rule (`Run.send_mustFail`,
    `resolvedStepOutput_select_mustFail`) and the phase rule of a quiet statement
    (`SelectReady.of_phases`, `queryContext_of_quiet`): over every database, `SELECT abs(1)` returns the one
    row 1, `SELECT abs(-9223372036854775808)` returns no result and the error of a failing function, and
    `WHERE 0` skips that call and makes the result empty. The instances check each claim and the negation
    of the two other claims. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectFunctionFaultCases", 3),), timeout=90)
