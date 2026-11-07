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
