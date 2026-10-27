"""Actual Lean server go-to-definition for table names after `ALTER TABLE ... RENAME TO` (editor task, part 3)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer
from tests.surface_editor_support import definitions, range_of

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT); CREATE TABLE keep(x)"
def moved : Database := db! r"CREATE TABLE draft(id INTEGER); ALTER TABLE draft RENAME TO final_name;
  CREATE TABLE side(x); ALTER TABLE side RENAME TO side_two; DROP TABLE side_two;
  CREATE TABLE twice(y); ALTER TABLE twice RENAME TO thrice; ALTER TABLE thrice RENAME TO fourth"
def chain := sql! shop r"ALTER TABLE items RENAME TO things; SELECT * FROM things;
  ALTER TABLE things RENAME TO stuff; SELECT * FROM stuff; SELECT * FROM keep"
def afterDrop := sql! shop r"ALTER TABLE items RENAME TO gone; DROP TABLE gone; CREATE TABLE gone(z);
  SELECT * FROM gone"
def reused := sql! shop r"ALTER TABLE items RENAME TO other; CREATE TABLE items(q);
  SELECT * FROM items; SELECT * FROM other"
def rolledBack := sql! shop r"BEGIN; ALTER TABLE items RENAME TO moved; ALTER TABLE keep RENAME TO items; ROLLBACK;
  SELECT * FROM items; SELECT * FROM keep"
def dropColumn := sql! shop r"ALTER TABLE items DROP COLUMN name; SELECT * FROM items"
def scripted := sql! moved r"SELECT * FROM final_name; SELECT * FROM fourth"
def finished : Nat := 0
'''


def test_origin_moves_with_a_rename(runtime_root: Path, tmp_path: Path) -> None:
    """Our origins after a rename (`SqlTableOrigins.stepOriginSources` for `sql!`, `stepCreatedSlots` for
    `db!`) reach the real server as go-to-definition targets: a renamed table of the database keeps the
    `CREATE TABLE` of the old name, also after a second rename, a table that the database text created and
    renamed navigates to its `CREATE TABLE` (also after two renames), and `DROP COLUMN` keeps the origin. A
    table that a later statement drops and creates again, and an old name that a statement creates again,
    have no target, and the new name of the recreated old name still has one. After a `ROLLBACK` a name that
    the transaction renamed has no target, instead of the target of the table that it named inside the transaction."""
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture")
    try:
        uri = server.open(SOURCE)
        items = (uri, range_of(SOURCE, "items(id", "items"))
        assert definitions(server, uri, SOURCE, "items RENAME TO things") == [items]
        assert definitions(server, uri, SOURCE, "things;\n  ALTER") == [items]
        assert definitions(server, uri, SOURCE, "stuff; SELECT", 1) == [items]
        assert definitions(server, uri, SOURCE, "keep\"") == [(uri, range_of(SOURCE, "keep(x)", "keep"))]
        assert definitions(server, uri, SOURCE, "gone\"") == []
        assert definitions(server, uri, SOURCE, "items; SELECT * FROM other") == []
        assert definitions(server, uri, SOURCE, "other\"") == [items]
        assert definitions(server, uri, SOURCE, "items\"") == [items]
        assert definitions(server, uri, SOURCE, "items; SELECT * FROM keep\"") == []
        assert definitions(server, uri, SOURCE, "keep\"", 1) == []
        assert definitions(server, uri, SOURCE, "final_name;", 1) == [(uri, range_of(SOURCE, "draft(id", "draft"))]
        assert definitions(server, uri, SOURCE, "fourth\"", 1) == [(uri, range_of(SOURCE, "twice(y", "twice"))]
    finally:
        server.close()
