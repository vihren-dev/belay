"""The comparison form of an unreadable view in the judge (`judge.catalog`), ADR 0011 and ADR 0019.

SQLite cannot read a view over a missing table, in a cycle or with a failing body. A recording
keeps such a view with the primary result code and the message of SQLite; the judge compares the
code only, so a prediction needs no knowledge of the wording of SQLite's messages.
"""

import pytest

from judge.catalog import tables_form

pytestmark = pytest.mark.unit


def unreadable(name: str, code: int, message: str = "no such table: main.missing") -> dict[str, object]:
    """An unreadable view as the native recorder writes it."""
    return {"name": name, "kind": "view", "unreadable": {"primaryCode": code, "message": message}}


def test_only_the_code_of_an_unreadable_view_is_compared() -> None:
    """The form keeps the kind and the code, and drops the message, so a prediction without it agrees."""
    recorded = tables_form({"tables": [unreadable("V", 1)]})
    predicted = tables_form({"tables": [unreadable("v", 1, "another wording")]})
    assert recorded == predicted == {"v": {"kind": "view", "unreadable": 1}}


def test_a_different_code_is_a_different_form() -> None:
    """An unreadable view with another result code is not the same observation."""
    assert tables_form({"tables": [unreadable("v", 1)]}) != tables_form({"tables": [unreadable("v", 18)]})


@pytest.mark.parametrize("damaged", [
    {"name": "t", "kind": "table", "unreadable": {"primaryCode": 1}},
    {"name": "v", "kind": "view", "unreadable": {"primaryCode": "1"}},
    {"name": "v", "kind": "view", "unreadable": {"message": "no code"}},
    {"name": "v", "kind": "view", "unreadable": 1},
])
def test_a_malformed_unreadable_object_is_refused(damaged: dict[str, object]) -> None:
    """Only a view with an integer primary code is an unreadable observation."""
    with pytest.raises(ValueError, match="unreadable object must be a view with an integer primaryCode"):
        tables_form({"tables": [damaged]})
