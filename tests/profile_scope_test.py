"""The scope of records by their execution profile (`conformance.profile_scope`).

These tests check the rule of ADR 0014, slice 4, for foreign keys: a record without an
execution profile (versions 1 to 3) may have turned foreign keys on in its setup, which the
subject cannot see, so such a record with a foreign key stays out of scope; a profiled
record, and a record without a foreign key, stay in scope.
"""

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.located import leaf
from conformance.profile_scope import foreign_key_scope, has_foreign_key

pytestmark = [pytest.mark.unit]

REFERENCES = leaf({"createTable": {"columns": [{"constraints": [{"references": {"table": "p", "columns": []}}]}]}}, 0, 1)
"""A CREATE TABLE whose column has a `REFERENCES` constraint."""
FOREIGN_KEY = leaf({"createTable": {"constraints": [{"foreignKey": {"columns": ["a"], "table": "p"}}]}}, 0, 1)
"""A CREATE TABLE with a `FOREIGN KEY` table constraint."""
PLAIN = leaf({"createTable": {"columns": [{"constraints": [{"notNull": {"algorithm": None}}]}]}}, 0, 1)
"""A CREATE TABLE without a foreign key."""


def test_foreign_keys_are_found_in_columns_and_table_constraints() -> None:
    """Both forms of a foreign key count, and other constraints do not."""
    assert has_foreign_key([REFERENCES]) and has_foreign_key([FOREIGN_KEY]) and not has_foreign_key([PLAIN])


@pytest.mark.parametrize("version", [1, 2, 3])
def test_a_record_without_profile_and_with_a_foreign_key_is_out_of_scope(version: int) -> None:
    """A record before version 4 with a foreign key is UNSUPPORTED, with the reason."""
    with pytest.raises(SqlError) as raised:
        foreign_key_scope({"name": "case", "nativeVersion": version}, [PLAIN, FOREIGN_KEY])
    assert raised.value.status == "UNSUPPORTED" and "foreign keys" in str(raised.value)


@pytest.mark.parametrize(("version", "statements"), [(4, [REFERENCES]), (5, [FOREIGN_KEY]), (3, [PLAIN]), (1, [])])
def test_profiled_records_and_records_without_foreign_keys_stay_in_scope(version: int, statements: list) -> None:
    """A profiled record says whether foreign keys are on, and a record without a foreign key
    does not depend on it."""
    foreign_key_scope({"name": "case", "nativeVersion": version}, statements)
