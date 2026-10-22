"""Single-table queries agree with native SQLite (ADR 0012, slice 1).

Each query is recorded with its outputs by `conformance.native_record.record_sql`,
mapped by the text package's translation, resolved by `Resolution/Queries.lean` and
evaluated by `QueryEval.lean`; the compiled runner compares the result rows with
the rules of ADR 0005 (multisets, tie groups) and the database state.
"""

from pathlib import Path

import pytest

from conformance.model_check import compiled
from conformance.native_record import record_sql
from conformance.native_replay import prepare
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
SCHEMA = ("CREATE TABLE t(Abc INTEGER, b TEXT, c); INSERT INTO t VALUES(1,'x',NULL),(2,'y',2.5),"
          "(1,'z','q'),(NULL,'w',X'00'),(3,NULL,1);")
"""A table with NULL, integer, REAL, text and blob values, and a repeated key."""


@pytest.mark.parametrize("query", [
    "SELECT * FROM t;",
    "SELECT b, abc FROM t WHERE abc = 1;",
    "SELECT count(*) FROM t WHERE b IS NULL OR abc > 2;",
    "SELECT abc = 1, b IS NOT NULL, NOT abc < 2 FROM t;",
    "SELECT c FROM t ORDER BY c;",
    "SELECT max(c), min(c), count(c), count(*) FROM t;",
    "SELECT count(*) FROM t WHERE 0 = 1;",
    "SELECT b AS k FROM t ORDER BY k DESC;",
    "SELECT abc, count(*) FROM t GROUP BY abc;",
    "SELECT missing FROM t;",
    "SELECT * FROM t ORDER BY 5;",
    "SELECT count(*) FROM t WHERE count(*) > 1;",
])
def test_query_agrees_with_sqlite(runtime_root: Path, query: str) -> None:
    """The model's result rows, column names and errors agree with the recorded native ones."""
    record = record_sql(SCHEMA, query, name="query", outputs=True)
    case, answer = prepare(record, runtime_translator(runtime_root))
    assert case is not None, answer
    assert compiled(case, runtime_root)["verdict"] == "AGREE"


def test_wrong_rows_disagree(runtime_root: Path) -> None:
    """A changed native result row makes the case disagree, so the comparison reads the rows."""
    record = record_sql(SCHEMA, "SELECT b FROM t WHERE abc = 1;", name="query", outputs=True)
    record["trace"][0]["rows"][0][0] = {"text": {"bytes": list(b"other")}}
    case, answer = prepare(record, runtime_translator(runtime_root))
    assert case is not None, answer
    assert compiled(case, runtime_root)["verdict"] == "DISAGREE"
