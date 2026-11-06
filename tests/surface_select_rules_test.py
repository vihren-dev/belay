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
