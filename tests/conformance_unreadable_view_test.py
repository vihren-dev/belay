"""A view that SQLite cannot read stays evidence outside the table replay."""

from pathlib import Path

import pytest

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
