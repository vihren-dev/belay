"""Actual Lean server observations of the order warning of `INSERT ... SELECT` (editor task, part 3)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, position

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def pair : Database := db! r"CREATE TABLE t(a INTEGER); CREATE TABLE sink(a INTEGER);
  INSERT INTO t VALUES (1), (2);
  INSERT INTO sink SELECT a FROM t LIMIT 1 /* db_limit */;
  INSERT INTO sink SELECT a FROM t LIMIT 1 OFFSET 1 /* db_offset */;
  INSERT INTO sink SELECT a FROM t UNION SELECT a + 1 FROM t LIMIT 1 /* db_compound */;
  INSERT INTO sink SELECT a FROM t ORDER BY a LIMIT 1 /* db_sorted */;
  INSERT INTO sink SELECT a FROM t /* db_all */;
  INSERT INTO sink SELECT 1 LIMIT 1 /* db_no_source */;
  INSERT INTO sink VALUES (3) /* db_values */;
  SELECT a AS evidence FROM t LIMIT 1"
def risky := sql! pair r"INSERT INTO sink SELECT a FROM t LIMIT 1 /* sql_bang */;
  INSERT INTO sink SELECT a FROM t ORDER BY a LIMIT 1 /* sql_sorted */"
def plain := sql r"INSERT INTO sink SELECT a FROM t LIMIT 1 OFFSET 1 /* plain_use */"
#sql pair r"INSERT INTO sink SELECT a FROM t LIMIT 1 /* command_run */"
def lowest : Int64 := 0
#sql pair r"INSERT INTO sink SELECT a FROM t WHERE a > $lowest LIMIT 1 /* command_parameter */"
set_option sql.orderWarnings false in
def quiet := sql r"INSERT INTO sink SELECT a FROM t LIMIT 1 /* quiet_use */"
def finished : Nat := 0
'''

def statement_start(marker: str) -> tuple[int, int]:
    """The (line, UTF-16 column) of the INSERT statement that the comment `marker` ends."""
    offset = SOURCE.rindex("INSERT INTO", 0, SOURCE.index(f"/* {marker} */"))
    before = SOURCE[:offset]
    return before.count("\n"), len(before.rsplit("\n", 1)[-1].encode("utf-16-le")) // 2


INSERT_WARNINGS = ("db_limit", "db_offset", "db_compound", "sql_bang", "plain_use", "command_run",
                   "command_parameter")


def test_insert_select_order_warning_in_every_context(runtime_root: Path, tmp_path: Path) -> None:
    """Our syntactic order warning for `INSERT ... SELECT` (`SqlOrderWarnings.orderRunWarnings` and
    `orderRiskWarnings`) reaches the real server in each context: `db!` and `#sql` (which run their
    statements, and whose output of an insert holds no alternatives), a `#sql` script with a parameter,
    `sql!` and plain `sql` give the warning at the statement, once, and it says the inserted rows may
    depend on an order and claims no distinct result. A query with `ORDER BY`, without `LIMIT`/`OFFSET`,
    without a source, a plain `VALUES` insert and the option turned off give none. The evidence warning of
    a `SELECT` in `db!` stays. Nothing becomes an error."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        found = diagnostics(server, uri)
        assert all(item["severity"] in (2, 3) for item in found), found
        warnings = [item for item in found if item["severity"] == 2]
        by_start = {(item["range"]["start"]["line"], item["range"]["start"]["character"]): item["message"]
                    for item in warnings}
        assert len(by_start) == len(warnings) == len(INSERT_WARNINGS) + 1, warnings
        for marker in INSERT_WARNINGS:
            message = by_start[statement_start(marker)]
            assert message.startswith("this statement inserts the rows of a query that takes rows with LIMIT or OFFSET"), message
            assert "ORDER BY" in message and "may depend on an order" in message, message
            assert "different results" not in message and "results may be equal" in message, message
        evidence = position(SOURCE, "SELECT a AS evidence")
        assert "2 different results" in by_start[(evidence["line"], evidence["character"])]
    finally:
        server.close()
