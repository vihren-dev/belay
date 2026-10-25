"""A view that SQLite cannot read stays evidence outside the table replay."""

from pathlib import Path

import pytest

from conformance import native_observation
from conformance.native_connection import Connection, NativeError, library_path, load_library
from conformance.native_record import record_sql
from conformance.native_replay import prepare
from conformance.replay_scope import OBSERVED_VIEW_REASON
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]


def test_unreadable_view_record_is_outside_the_table_replay(runtime_root: Path) -> None:
    """The recorder keeps a view over a missing table with its error code and no table metadata;
    the table replay reports it as a view, in the same way as for a readable view."""
    record = record_sql("CREATE TABLE t(a);", "CREATE VIEW v AS SELECT * FROM missing;", name="unreadable-view")
    [unreadable] = [table for table in record["trace"][0]["visible"]["tables"] if table["kind"] == "view"]
    assert unreadable["unreadable"]["primaryCode"] == 1 and "withoutRowid" not in unreadable
    case, result = prepare(record, runtime_translator(runtime_root))
    assert case is None and result["verdict"] == "MODEL_UNSUPPORTED" and result["reason"] == OBSERVED_VIEW_REASON


@pytest.mark.parametrize("code", [1, 9, 10])
def test_only_sql_errors_of_a_view_are_evidence(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, code: int) -> None:
    """A SQL error (code 1) while the observation reads a view becomes unreadable-view evidence.
    An interrupt (9) or an I/O error (10) is an infrastructure failure: `observe` raises it."""
    def fail(*args: object, **kwargs: object) -> None:
        """Stand for a native read of the view that ends with the parametrized result code."""
        raise NativeError(code, "injected failure", "prepare")

    connection = Connection(load_library(library_path()), tmp_path / "views.db")
    connection.execute_script("CREATE VIEW v AS SELECT 1 AS x;")
    monkeypatch.setattr(native_observation, "observe_object", fail)
    if code == 1:
        [entry] = native_observation.observe(connection)["tables"]
        assert entry["unreadable"]["primaryCode"] == 1
    else:
        with pytest.raises(NativeError, match="injected failure"):
            native_observation.observe(connection)
