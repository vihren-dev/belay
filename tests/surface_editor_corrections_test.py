"""Actual Lean server observations of name corrections in `sql!`, `db!` and `#sql` text (editor task, part 2b)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics
from tests.surface_editor_support import corrections, span_of

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r##"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE, qty INTEGER, price REAL);
  CREATE TABLE tied(bat, cat); CREATE TABLE odd("select" INTEGER)"##
def unique := sql! shop r"SELECT lable FROM orders"
def tie := sql! shop r"SELECT aat FROM tied"
def distant := sql! shop r"SELECT far_away_name FROM orders"
def backticks := sql! shop r"SELECT `lable` FROM orders"
def brackets := sql! shop r"SELECT [prise] FROM orders"
def tables := sql! shop r"SELECT * FROM ordrs"
def quotedTable := sql! shop r##"SELECT * FROM "ordrs""##
def updates := sql! shop r"UPDATE orders SET qyt = 1"
def inserts := sql! shop r"INSERT INTO orders(lable) VALUES (1)"
def deletes := sql! shop r"DELETE FROM orders WHERE prce > 1"
def keyword := sql! shop r##"SELECT selec FROM odd"##
def keywordOneHash := sql! shop r#"SELECT selec FROM odd"#
def keywordRaw := sql! shop r"SELECT selec FROM odd"
def keywordOrdinary := sql! shop "SELECT selec FROM odd"
def escaped := sql! shop "SELECT\\nlable FROM orders"
def plain := sql r"SELECT lable FROM orders"
def building : Database := db! r"CREATE TABLE t(name); SELECT nmae FROM t"
#sql shop r"SELECT qyt FROM orders"
def finished : Nat := 0
'''


def test_corrections_offered(runtime_root: Path, tmp_path: Path) -> None:
    """Our correction candidates (`SqlNameCorrections`) reach the real server as quick fixes at the exact
    range of the written name: a unique nearest name, a tie, quoting kept as written, tables and column
    targets of writes, and no fix for a distant name, plain `sql`, an escaped literal, or a quoted name that would end the
    literal that holds it."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        assert corrections(server, uri, SOURCE, "lable FROM orders", 0, "lable") == [("Replace lable with label", "label")]
        assert corrections(server, uri, SOURCE, "aat", 0, "aat") == [
            ("Replace aat with bat", "bat"), ("Replace aat with cat", "cat")]
        assert corrections(server, uri, SOURCE, "far_away_name", 0, "far_away_name") == []
        assert corrections(server, uri, SOURCE, "`lable`", 0, "`lable`") == [("Replace `lable` with `label`", "`label`")]
        assert corrections(server, uri, SOURCE, "[prise]", 0, "[prise]") == [("Replace [prise] with [price]", "[price]")]
        assert corrections(server, uri, SOURCE, "ordrs", 0, "ordrs") == [("Replace ordrs with orders", "orders")]
        assert corrections(server, uri, SOURCE, '"ordrs"', 0, '"ordrs"') == [
            ('Replace "ordrs" with "orders"', '"orders"')]
        assert corrections(server, uri, SOURCE, "qyt", 0, "qyt") == [("Replace qyt with qty", "qty")]
        assert corrections(server, uri, SOURCE, "lable) VALUES", 0, "lable") == [("Replace lable with label", "label")]
        assert corrections(server, uri, SOURCE, "prce", 0, "prce") == [("Replace prce with price", "price")]
        assert corrections(server, uri, SOURCE, "nmae", 0, "nmae") == [("Replace nmae with name", "name")]
        assert corrections(server, uri, SOURCE, "qyt FROM", 0, "qyt") == [("Replace qyt with qty", "qty")]
        for occurrence in (0, 1):
            assert corrections(server, uri, SOURCE, "selec FROM odd", occurrence, "selec") == [
                ('Replace selec with "select"', '"select"')], occurrence
        for occurrence in (2, 3):
            assert corrections(server, uri, SOURCE, "selec FROM odd", occurrence, "selec") == [], occurrence
        for occurrence in (1, 2):
            assert corrections(server, uri, SOURCE, "lable FROM orders", occurrence, "lable") == [], occurrence
    finally:
        server.close()


def fresh_server(runtime_root: Path, directory: Path) -> LeanServer:
    """A server for another version of the source, with its own working directory."""
    directory.mkdir()
    return LeanServer(runtime_root, directory)


def apply_edit(source: str, edit_range: dict[str, dict[str, int]], text: str) -> str:
    """Apply one single-line LSP edit (UTF-16 columns) to the source."""
    lines = source.split("\n")
    line = edit_range["start"]["line"]
    units = lines[line].encode("utf-16-le")
    first, last = 2 * edit_range["start"]["character"], 2 * edit_range["end"]["character"]
    lines[line] = (units[:first] + text.encode("utf-16-le") + units[last:]).decode("utf-16-le")
    return "\n".join(lines)


APPLY = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT, qty INTEGER)"
def typo := sql! shop r"SELECT '😀', lable FROM orders WHERE qyt = 1"
def finished : Nat := 0
'''


@pytest.mark.parametrize("newline", ["\n", "\r\n"], ids=["lf", "crlf"])
def test_applied_correction_removes_the_error(runtime_root: Path, tmp_path: Path, newline: str) -> None:
    """The edit of our quick fix (`SqlNameInfo.suggestCorrections`) has the exact UTF-16 range after
    non-BMP text and with CRLF line ends: applying it makes the next typo of the statement visible, and
    applying that one makes the statement elaborate without errors."""
    source = APPLY.replace("\n", newline)
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(source)
        errors = [item for item in diagnostics(server, uri) if item["severity"] == 1]
        assert len(errors) == 1 and "lable" in errors[0]["message"], errors
        (title, text), = corrections(server, uri, source, "lable", 0, "lable")
        assert (title, text) == ("Replace lable with label", "label")
        edited = apply_edit(source, span_of(source, "lable", 0, "lable"), text)
        second = fresh_server(runtime_root, tmp_path / "second")
        try:
            uri = second.open(edited)
            errors = [item for item in diagnostics(second, uri) if item["severity"] == 1]
            assert len(errors) == 1 and "qyt" in errors[0]["message"], errors
            (title, text), = corrections(second, uri, edited, "qyt", 0, "qyt")
            assert (title, text) == ("Replace qyt with qty", "qty")
            fixed = apply_edit(edited, span_of(edited, "qyt", 0, "qyt"), text)
        finally:
            second.close()
        third = fresh_server(runtime_root, tmp_path / "third")
        try:
            uri = third.open(fixed)
            assert [item for item in diagnostics(third, uri) if item["severity"] == 1] == []
        finally:
            third.close()
    finally:
        server.close()


DOUBLE_QUOTED = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT, qty INTEGER)"
def fallback := sql! shop r##"SELECT "lable", "qtty" FROM orders"##
def existing := sql! shop r##"SELECT "label", 'lable', label AS "lable" FROM orders"##
def ambiguous := sql! shop r##"SELECT "id" FROM orders, orders AS again"##
def finished : Nat := 0
'''


def test_double_quoted_fallback_warning(runtime_root: Path, tmp_path: Path) -> None:
    """Our warning (`SqlNameInfo.doubleQuoteWarning`) appears at a double-quoted name that no column in
    scope has, which SQLite reads as a text literal, and comes with a correction. A column that exists,
    a single-quoted text, an alias declaration and an ambiguous name get no such warning."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(DOUBLE_QUOTED)
        warnings = [item for item in diagnostics(server, uri) if item["severity"] == 2]
        assert len(warnings) == 2, warnings
        expected = span_of(DOUBLE_QUOTED, '"lable"', 0, '"lable"')
        assert warnings[0]["range"] == expected, warnings
        assert "text literal 'lable'" in warnings[0]["message"], warnings
        assert warnings[1]["range"] == span_of(DOUBLE_QUOTED, '"qtty"', 0, '"qtty"'), warnings
        assert corrections(server, uri, DOUBLE_QUOTED, '"qtty"', 0, '"qtty"') == [
            ('Replace "qtty" with "qty"', '"qty"')]
        assert corrections(server, uri, DOUBLE_QUOTED, '"lable"', 0, '"lable"') == [
            ('Replace "lable" with "label"', '"label"')]
    finally:
        server.close()


KEYWORD = '''import Belay
open Belay.Sqlite
def shop : Database := db! r##"CREATE TABLE odd("select" INTEGER)"##
def keyword := sql! shop r#"SELECT selec FROM odd"#
def finished : Nat := 0
'''


def test_applied_quoted_correction_keeps_the_literal(runtime_root: Path, tmp_path: Path) -> None:
    """The quoted edit of our quick fix (`SqlLiteral.replacementKeepsLiteral`) in a raw literal with one
    `#`: applying it elaborates without errors, so the literal still ends where it did."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(KEYWORD)
        (title, text), = corrections(server, uri, KEYWORD, "selec FROM", 0, "selec")
        assert (title, text) == ('Replace selec with "select"', '"select"')
        fixed = apply_edit(KEYWORD, span_of(KEYWORD, "selec FROM", 0, "selec"), text)
    finally:
        server.close()
    second = fresh_server(runtime_root, tmp_path / "second")
    try:
        uri = second.open(fixed)
        assert [item for item in diagnostics(second, uri) if item["severity"] == 1] == []
    finally:
        second.close()
