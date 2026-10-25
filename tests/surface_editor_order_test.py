"""Actual Lean server observations of the order warnings of `db!`, `#sql`, `sql!` and `sql` (editor task, part 2a)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, position

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def pair : Database := db! r"CREATE TABLE t(a INTEGER); CREATE TABLE same(a INTEGER);
  CREATE TABLE single(a INTEGER);
  INSERT INTO t VALUES (1), (2);
  INSERT INTO same VALUES (7), (7);
  INSERT INTO single VALUES (5);
  SELECT a AS evidence FROM t LIMIT 1;
  SELECT a AS equal FROM same LIMIT 1;
  SELECT a AS lone FROM single LIMIT 1;
  SELECT a AS sorted FROM t ORDER BY a LIMIT 1"
def risky := sql! pair r"INSERT INTO t VALUES (3); SELECT a AS unknown_rows FROM t LIMIT 1"
def plain := sql r"SELECT a AS plain_risk FROM t LIMIT 1; SELECT 1 AS no_source LIMIT 1;
  SELECT a AS plain_sorted FROM t ORDER BY a LIMIT 1"
#sql pair r"SELECT a AS run_evidence FROM t LIMIT 1; SELECT a AS run_equal FROM same LIMIT 1"
def finished : Nat := 0
'''


def test_order_warnings_follow_the_context(runtime_root: Path, tmp_path: Path) -> None:
    """Our order warnings (`SqlOrderWarnings`, called by `db!`, `#sql`, `sql!` and `sql`) reach the real
    server: an actual alternative result in a context that runs gives the evidence warning at the
    statement, equal or single results give none, a context that does not run gives only the risk
    warning that claims no distinct result, a query with `ORDER BY` or without a source gives none, and
    `#sql` warns once. Nothing becomes an error."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        found = diagnostics(server, uri)
        assert all(item["severity"] in (2, 3) for item in found), found
        warnings = {(item["range"]["start"]["line"], item["range"]["start"]["character"]): item["message"]
                    for item in found if item["severity"] == 2}
        expected = {"evidence": "evidence", "unknown_rows": "risk", "plain_risk": "risk", "run_evidence": "evidence"}
        assert len(warnings) == len(expected) == len([item for item in found if item["severity"] == 2]), found
        for alias, kind in expected.items():
            start = position(SOURCE, f"SELECT a AS {alias}")
            message = warnings[(start["line"], start["character"])]
            assert "LIMIT or OFFSET" in message and "ORDER BY" in message, message
            if kind == "evidence":
                assert "2 different results" in message, message
            else:
                assert "may depend on an order" in message and "different results" not in message, message
    finally:
        server.close()
