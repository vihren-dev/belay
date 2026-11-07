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
