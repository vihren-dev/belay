"""Actual Lean server observations of table information in the contexts that run their statements (editor task, part 2a)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, table_hover

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT);
  INSERT INTO orders VALUES (1, 'a');
  INSERT INTO orders VALUES (2, 'b');
  SELECT * FROM orders AS db_read"
#sql shop r"SELECT * FROM orders AS first_read;
  INSERT INTO orders VALUES (3, 'c');
  SELECT * FROM orders AS second_read;
  DELETE FROM orders WHERE 1;
  SELECT * FROM orders AS third_read"
def unrun := sql! shop r"INSERT INTO orders VALUES (9, 'z'); SELECT * FROM orders AS unrun_read"
def finished : Nat := 0
'''


def test_executed_contexts_know_their_rows(runtime_root: Path, tmp_path: Path) -> None:
    """Our contexts that run their statements (`executedContexts`, used by `db!` and `#sql`) reach the
    real server: the hover of a table name shows the rows that the run reached before the statement,
    also after a write, where `sql!` knows no count. The `#sql` output stays an information message."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        for spelling, count in (("orders VALUES (1", "0 rows"), ("orders VALUES (2", "1 row"),
                                ("orders AS db_read", "2 rows"), ("orders AS first_read", "2 rows"),
                                ("orders VALUES (3", "2 rows"), ("orders AS second_read", "3 rows"),
                                ("orders WHERE 1", "3 rows"), ("orders AS third_read", "0 rows"),
                                ("orders VALUES (9", "2 rows")):
            text = table_hover(server, uri, SOURCE, spelling, 0, "orders")
            assert f"{count} at this point of the script." in text, (spelling, text)
        assert "at this point of the script" not in table_hover(server, uri, SOURCE, "orders AS unrun_read", 0, "orders")
        server.request("textDocument/documentSymbol", {"textDocument": {"uri": uri}}, timeout=60)
        diagnostics = [item for message in server.notifications
                       if message.get("method") == "textDocument/publishDiagnostics"
                       for item in message["params"]["diagnostics"]]
        assert all(item["severity"] == 3 for item in diagnostics), diagnostics
    finally:
        server.close()
