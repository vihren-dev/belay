"""The authored cases of parameters (`conformance.authored_parameters`) give SQLite the inputs that
plans/20261023-parameters.task.md describes.

Native SQLite is the oracle: these tests record each case and check that the case reaches the
outcome it is written for, such as a distinct value for each number, a `datatype mismatch` for each
refused window value, and SQLite's message for each prepare error. The task's mutants must each
change the result of a case, so the tests also check that the native results differ from what each
mutant would give.
"""

import pytest

from conformance.authored_parameters import definitions, records
from conformance.case_format import Json
from conformance.native_bindings import decode_rows
from conformance.native_connection import Cell

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_native("sqlite3")]


@pytest.fixture(scope="module")
def recorded() -> dict[str, dict[str, Json]]:
    """Record every case once, by name."""
    acquired = records()
    assert len({record["name"] for record in acquired}) == len(acquired) == len(definitions())
    return {record["name"]: record for record in acquired}


def plain(cell: Cell) -> object:
    """A recorded integer or text cell as a Python value, for short expectations."""
    kind, payload = cell
    return payload.decode() if kind == 3 and isinstance(payload, bytes) else payload


def results(record: dict[str, Json]) -> list[list[tuple[object, ...]]]:
    """The rows of each statement of a recorded case, as Python values."""
    return [[tuple(plain(cell) for cell in row) for row in decode_rows(event["rows"])] for event in record["trace"]]


def errors(record: dict[str, Json]) -> list[tuple[int, str, str | None]]:
    """The primary code, message and phase of each statement of a recorded case."""
    return [(event["primaryCode"], event["error"], event["phase"]) for event in record["trace"]]


def test_numbering_gives_each_number_its_value(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 2: a `?` after `?5` is 6, not 3, and `:a`, `@a` and `$a` are different names, which
    kills the mutants that number `?` from the count of parameters and that join `:a` and `@a`."""
    assert results(recorded["parameter-numbers-mixed"]) == [[(10, 50, 60, 70, 80, 90, 70)]]
    assert results(recorded["parameter-numbers-name-after-number"]) == [[(30, 40, 10, 40, 50)]]
    assert results(recorded["parameter-numbers-each-statement"]) == [[(1, 2)], [(4, 5)], [(6, 6)], [("none",)]]
    assert len(recorded["parameter-numbers-mixed"]["trace"][0]["parameters"]) == 9


def test_places_read_the_bound_values(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 3: a trigger reads the value that the INSERT bound, and an upsert's DO UPDATE and its
    WHERE read their parameters."""
    assert results(recorded["parameter-place-trigger-write"])[-1] == [(8,), (42,)]
    assert results(recorded["parameter-place-upsert"]) == [[("a", "set-new")], []]
    assert all(code == 0 for name, record in recorded.items() if name.startswith("parameter-place-")
               for code, _, _ in errors(record))


def test_parameter_has_no_affinity(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 3: `?1 = '2'` is 0 for the integer 2, which kills the mutant that gives a parameter
    an affinity; a column applies its affinity and collation to the value."""
    assert results(recorded["parameter-no-affinity"]) == [[(0, 1, 0, 1, 1)]]
    assert results(recorded["parameter-column-affinity"]) == [[(1, 1, 0, 1, 1)]]
    assert results(recorded["parameter-collation"]) == [[(0, 1, 1, 1, 1)]]


def test_order_and_group_by_a_value(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 4: `ORDER BY ?1` bound to 1 keeps the order of the rows, and with `LIMIT 1` the first
    row, while `ORDER BY 1` sorts them, which kills the mutant that reads the value as a column number; `GROUP BY ?1` gives one
    group, and none over no rows."""
    assert results(recorded["parameter-order-by"]) == [[(30, 1), (10, 1), (20, 1)], [(30, 1)], [(10,), (20,), (30,)]]
    assert results(recorded["parameter-group-by"]) == [[(3, 30)], []]


def test_windows_accept_integer_values(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 5: each accepted LIMIT and OFFSET value gives its window, a negative LIMIT has no
    limit, a negative OFFSET skips no rows, and `LIMIT 0` does not read its OFFSET."""
    limits = results(recorded["parameter-limit-accepted"])
    assert limits == [[(1,), (2,)]] * 7 + [[(1,), (2,), (3,), (4,), (5,)], [(1,)]]
    assert results(recorded["parameter-offset-accepted"]) == [[(2,), (3,)]] * 4 + [[(1,), (2,)]]
    assert errors(recorded["parameter-limit-zero-skips-offset"]) == [(0, "", None)] * 2
    assert results(recorded["parameter-limit-comma"]) == [[(2,), (3,)]]


def test_windows_refuse_other_values(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 5: each refused value fails the statement when it runs, which kills the mutant whose
    LIMIT accepts a real with a fraction; OFFSET is read after a LIMIT that is not 0 and over no rows."""
    refused = [name for name in recorded if "-refused-" in name or name.startswith("parameter-offset-read-")]
    assert len(refused) == 14
    for name in refused:
        assert errors(recorded[name]) == [(20, "datatype mismatch", "step")], name


def test_prepare_errors_have_sqlite_messages(recorded: dict[str, dict[str, Json]]) -> None:
    """Outcome 6: each place that refuses a parameter fails at prepare with SQLite's message."""
    expected = {"trigger-body": "trigger cannot use variables", "trigger-when": "trigger cannot use variables",
                "default": "default value of column [x] is not constant",
                "check": "parameters prohibited in CHECK constraints",
                "generated": "parameters prohibited in generated columns",
                "index-expression": "parameters prohibited in index expressions",
                "partial-index": "parameters prohibited in partial index WHERE clauses"}
    for name, message in expected.items():
        assert errors(recorded[f"parameter-prepare-{name}"]) == [(1, message, "prepare")], name
