"""Actual Lean server go-to-definition for the origin of table names in `sql!` text (editor task, part 2a)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, compile_helper_module, hover, position

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

HELPER = '''import Belay
open Belay.Sqlite
def helperShop : Database := db! r"CREATE TABLE ledger(id INTEGER PRIMARY KEY)"
'''

SOURCE = '''import Belay
import OriginHelper
open Belay.Sqlite
def firstShop : Database := db! r"CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT);
  CREATE TABLE only_first(x)"
def secondShop : Database := db! r"CREATE TABLE items(id INTEGER PRIMARY KEY, price REAL)"
def renamed := firstShop
def rebuilt : Database := db! r"CREATE TABLE items(a); DROP TABLE items; CREATE TABLE items(b)"
def computed : Database := id firstShop
def inFirst := sql! firstShop r"SELECT * FROM items; SELECT * FROM only_first"
def inSecond := sql! secondShop r"SELECT * FROM items"
def inAlias := sql! renamed r"SELECT * FROM items"
def inRebuilt := sql! rebuilt r"SELECT * FROM items"
def inComputed := sql! computed r"SELECT * FROM items"
def inImported := sql! helperShop r"SELECT * FROM ledger"
def inSequence := sql! firstShop r"DROP TABLE items; CREATE TABLE items(z); SELECT * FROM items"
def finished : Nat := 0
'''


def range_of(text: str, spelling: str, token: str, occurrence: int = 0) -> dict[str, object]:
    """The LSP range of `token`, which starts at the beginning of the `occurrence` of `spelling`."""
    start = position(text, spelling, occurrence)
    return {"start": start, "end": {**start, "character": start["character"] + len(token)}}


def definitions(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int = 0
                ) -> list[tuple[str, dict[str, object]]]:
    """The targets of a go-to-definition request at the occurrence, as (document, range) pairs."""
    result = server.request("textDocument/definition", {"textDocument": {"uri": uri},
                                                         "position": position(source, spelling, occurrence)})
    assert isinstance(result, list), result
    targets = []
    for item in result:
        assert isinstance(item, dict), item
        targets.append((item.get("targetUri") or item["uri"], item.get("targetSelectionRange") or item["range"]))
    return targets


def test_table_origins_navigate(runtime_root: Path, tmp_path: Path) -> None:
    """Our table origins (`SqlTableOrigins`, the environment extension and `registerTableOrigins`
    in `db!`) reach the real server as go-to-definition targets: the CREATE TABLE of the right
    database when two databases share a table name, through a constant that names another one, in
    an imported module and after a DROP and CREATE in the database text. A computed database and a
    table that a statement of the script creates again have no target."""
    modules = compile_helper_module(runtime_root, tmp_path, "OriginHelper", HELPER)
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture", extra_modules=modules)
    try:
        uri = server.open(SOURCE)
        assert uri == (tmp_path / "EditorFixture.lean").as_uri()
        helper_uri = (tmp_path / "OriginHelper.lean").as_uri()
        first_items = range_of(SOURCE, "items(id INTEGER PRIMARY KEY, name", "items")
        second_items = range_of(SOURCE, "items(id INTEGER PRIMARY KEY, price", "items")
        assert definitions(server, uri, SOURCE, "items; SELECT * FROM only_first") == [(uri, first_items)]
        assert definitions(server, uri, SOURCE, "only_first\"") == [
            (uri, range_of(SOURCE, "only_first(x)", "only_first"))]
        assert definitions(server, uri, SOURCE, "items\"", 0) == [(uri, second_items)]
        assert definitions(server, uri, SOURCE, "items\"", 1) == [(uri, first_items)]
        assert definitions(server, uri, SOURCE, "items\"", 2) == [(uri, range_of(SOURCE, "items(b)", "items"))]
        assert definitions(server, uri, SOURCE, "items\"", 3) == []
        assert definitions(server, uri, SOURCE, "ledger\"") == [
            (helper_uri, range_of(HELPER, "ledger(id", "ledger"))]
        assert definitions(server, uri, SOURCE, "items; CREATE TABLE items(z)") == [(uri, first_items)]
        assert definitions(server, uri, SOURCE, "items\"", 4) == []
        text = hover(server, uri, position(SOURCE, "items\"", 2))["contents"]
        assert isinstance(text, dict) and text["value"].startswith("Table `items` of `rebuilt`."), text
    finally:
        server.close()
