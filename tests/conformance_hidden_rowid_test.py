"""A case whose table hides its rowid behind columns named rowid, _rowid_ and oid
(`conformance.native_replay.HiddenRowid`).

Since triggers reach the model (ADR 0018, slice 5), the upstream case `triggerD-1.2` gets past
the frontend; the replay must report it as out of scope, as the model refuses such column names,
not as a harness error.
"""

from pathlib import Path

import pytest

from conformance.native_record import record_sql
from conformance.native_replay import HIDDEN_ROWID_REASON, prepare
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]


def test_hidden_rowid_is_out_of_scope(runtime_root: Path) -> None:
    """`prepare` gives the verdict MODEL_UNSUPPORTED with the reason of the column names."""
    record = record_sql("CREATE TABLE t1(rowid, oid, _rowid_, x); CREATE TABLE log(a, b);"
                        "CREATE TRIGGER r1 AFTER INSERT ON t1 BEGIN INSERT INTO log VALUES (new.rowid, new.x); END;",
                        "INSERT INTO t1 VALUES (100, 200, 300, 400);", name="hidden-rowid")
    case, result = prepare(record, runtime_translator(runtime_root))
    assert case is None and result["verdict"] == "MODEL_UNSUPPORTED" and result["reason"] == HIDDEN_ROWID_REASON
