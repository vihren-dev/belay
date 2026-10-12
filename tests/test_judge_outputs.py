"""Statement output comparison of the judge (`judge.outputs.matches_output`), the ADR 0005 rule.

The rule decides AGREE or DISAGREE for every statement output, so each case below would
change a verdict if the rule changed.
"""

import pytest

from judge.outputs import matches_output

ONE, TWO, THREE = [{"integer": {"value": 1}}], [{"integer": {"value": 2}}], [{"integer": {"value": 3}}]


def output(*rows: list[object]) -> dict[str, object]:
    """A one-column SELECT output with the given rows."""
    return {"columns": ["x"], "rows": list(rows), "changes": None}


@pytest.mark.unit
def test_bag_without_groups() -> None:
    """Without ORDER BY, the rows compare as a bag: order is free, multiplicity is not."""
    assert matches_output(output(ONE, TWO), output(TWO, ONE), None)
    assert not matches_output(output(ONE, ONE), output(ONE, TWO), None)
    assert not matches_output(output(ONE), output(ONE, ONE), None)


@pytest.mark.unit
def test_empty_ordered_result() -> None:
    """An empty ordered result, such as `LIMIT 0`, agrees with an empty prediction."""
    assert matches_output(output(), output(), [])
    assert not matches_output(output(), output(ONE), [])


@pytest.mark.unit
def test_tie_groups_keep_order_and_allow_permutation_within() -> None:
    """Groups keep their order; rows of one tie group may come in any order."""
    groups = [{"rows": [ONE, TWO], "count": 2}, {"rows": [THREE], "count": 1}]
    assert matches_output(output(ONE, TWO, THREE), output(TWO, ONE, THREE), groups)
    assert not matches_output(output(ONE, TWO, THREE), output(THREE, ONE, TWO), groups)


@pytest.mark.unit
def test_window_cuts_only_the_boundary_groups() -> None:
    """A window may take part of the last group, but a middle group must be complete."""
    cut = [{"rows": [ONE], "count": 1}, {"rows": [TWO, THREE], "count": 1}]
    assert matches_output(output(ONE, TWO), output(ONE, THREE), cut)
    middle = [{"rows": [ONE], "count": 1}, {"rows": [TWO, THREE], "count": 1}, {"rows": [ONE], "count": 1}]
    assert not matches_output(output(ONE, TWO, ONE), output(ONE, TWO, ONE), middle)


@pytest.mark.unit
def test_shape_and_change_count() -> None:
    """Columns and the direct change count must be equal; ragged rows never agree."""
    assert not matches_output(output(ONE), {**output(ONE), "columns": ["y"]}, None)
    assert not matches_output({**output(), "changes": 1}, {**output(), "changes": 0}, None)
    assert not matches_output(output(ONE + TWO), output(ONE + TWO), None)
