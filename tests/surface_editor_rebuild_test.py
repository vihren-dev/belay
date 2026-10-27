"""Actual Lean server observations of the table rebuild of the guide and of DROP COLUMN (editor task, part 3)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, table_hover
from tests.surface_editor_support import definitions, range_of

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

REBUILD = '''CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT);
  INSERT INTO p_new SELECT id, name FROM p;
  DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT'''

SOURCE = f'''import Belay
open Belay.Sqlite
def family : Database := db! r"CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT, extra INTEGER);
  INSERT INTO p VALUES(1,'x',10),(2,'y',20);
  CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER REFERENCES p(id) ON DELETE CASCADE, note TEXT)"
def rebuild := sql! family r"BEGIN;
  {REBUILD};
  SELECT id, name FROM p /* after_rebuild */"
def rebuilt : Database := db! r"CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT, extra INTEGER);
  INSERT INTO p VALUES(1,'x',10),(2,'y',20);
  BEGIN;
  {REBUILD}"
def after := sql! rebuilt r"SELECT * FROM p /* after_db */"
def single : Database := db! r"CREATE TABLE q(id INTEGER PRIMARY KEY, name TEXT, extra INTEGER)"
def dropped := sql! single r"ALTER TABLE q DROP COLUMN extra; SELECT * FROM q /* after_drop */"
def finished : Nat := 0
'''


def test_rebuild_script_hovers_and_navigation(runtime_root: Path, tmp_path: Path) -> None:
    """Our editor information for the guide's rebuild script (`INSERT ... SELECT`, `DROP TABLE`, `ALTER TABLE ...
    RENAME TO`) reaches the real server. In `sql!` over the database that has the parent, the source of the copy
    and the dropped table navigate to the `CREATE TABLE` of the database, the new table navigates to its own
    `CREATE TABLE` only in the script that `db!` records, and the name `p` after the rename has no target in
    `sql!` (the script created the table). In `db!`, the `INSERT ... SELECT` shows the rows that the run
    reached, and a later `sql!` on that database navigates `p` to the `CREATE TABLE p_new` that made the table.
    `DROP COLUMN` keeps the origin and the hover after it lists the remaining columns. No diagnostic is an error."""
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture")
    try:
        uri = server.open(SOURCE)
        family_p = (uri, range_of(SOURCE, "p(id INTEGER PRIMARY KEY, name TEXT, extra", "p"))
        target = table_hover(server, uri, SOURCE, "p_new SELECT", 0, "p_new")
        assert target.startswith("Table `p_new` of `family`.") and "at this point of the script" not in target, target
        source = table_hover(server, uri, SOURCE, "p;\n  DROP", 0, "p")
        assert "`extra`: INTEGER" in source and "at this point of the script" not in source, source
        assert definitions(server, uri, SOURCE, "p;\n  DROP") == [family_p]
        assert definitions(server, uri, SOURCE, "p; ALTER TABLE p_new") == [family_p]
        assert definitions(server, uri, SOURCE, "p_new SELECT") == []
        final = table_hover(server, uri, SOURCE, "p /* after_rebuild */", 0, "p")
        assert "`extra`" not in final and "`name`: TEXT" in final, final
        assert definitions(server, uri, SOURCE, "p /* after_rebuild */") == []
        run_target = table_hover(server, uri, SOURCE, "p_new SELECT", 1, "p_new")
        assert "0 rows at this point of the script." in run_target, run_target
        run_source = table_hover(server, uri, SOURCE, "p;\n  DROP", 1, "p")
        assert "2 rows at this point of the script." in run_source, run_source
        created = (uri, range_of(SOURCE, "p_new(id", "p_new", 1))
        assert definitions(server, uri, SOURCE, "p /* after_db */") == [created]
        assert "`extra`" not in table_hover(server, uri, SOURCE, "p /* after_db */", 0, "p")
        single_q = (uri, range_of(SOURCE, "q(id INTEGER PRIMARY KEY, name TEXT, extra", "q"))
        assert definitions(server, uri, SOURCE, "q DROP COLUMN") == [single_q]
        dropped = table_hover(server, uri, SOURCE, "q /* after_drop */", 0, "q")
        assert "`extra`" not in dropped and "`id`: INTEGER, PRIMARY KEY" in dropped, dropped
        assert definitions(server, uri, SOURCE, "q /* after_drop */") == [single_q]
        assert not [item for item in diagnostics(server, uri) if item["severity"] == 1]
    finally:
        server.close()
