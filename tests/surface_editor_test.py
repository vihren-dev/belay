"""Actual Lean server observations of SQL parameters and exact source ranges."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, hover, position, semantic_tokens

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def greeting : String := "hello"
def captured (amount : Int64) : Script :=
  sql r##"SELECT '😀', $amount, $amount,
    $greeting"##
def nested : Id Script := do
  let next : String := "next"
  return sql r"SELECT $next, $next"
def named := sql r"SELECT :name, :name, ?3, ?3; SELECT @other, #hash, ?3"
def aliases := sql "SELECT ?, ?1, ?5"
def shifted := sql r"SELECT :shared; SELECT ?, :shared"
def direct (value : Value) := sql r"SELECT $value"
def escaped := sql "SELECT 'a\\nb', :hidden"
def finished : Nat := 0
'''


@pytest.mark.parametrize("newline", ["\n", "\r\n"], ids=["lf", "crlf"])
def test_sql_parameter_editor_information(runtime_root: Path, tmp_path: Path, newline: str) -> None:
    """Our emission reaches real hovers and tokens for repeated captures, do locals, constants,
    generated arguments, sparse slots, numbered aliases and each sign. Raw r##/ordinary strings
    retain UTF-16 ranges after non-BMP text; escaped literals gain no guessed token information."""
    source = SOURCE.replace("\n", newline)
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(source)
        cases = [("$amount", 0, "amount", "Int64", 1, True),
                 ("$amount", 1, "amount", "Int64", 1, True),
                 ("$greeting", 0, "greeting", "String", 2, False),
                 ("$next", 0, "next", "String", 1, True),
                 ("$next", 1, "next", "String", 1, True),
                 (":name", 0, "name", "Value", 1, True),
                 (":name", 1, "name", "Value", 1, True),
                 ("?3", 0, "p3", "Value", 3, True),
                 ("?3", 1, "p3", "Value", 3, True),
                 ("?3", 2, "p3", "Value", 3, True),
                 ("@other", 0, "other", "Value", 1, True),
                 ("#hash", 0, "hash", "Value", 2, True),
                 ("?,", 0, "p1", "Value", 1, True),
                 ("?1", 0, "p1", "Value", 1, True),
                 ("?5", 0, "p5", "Value", 5, True),
                 (":shared", 0, "shared", "Value", 1, True),
                 (":shared", 1, "shared", "Value", 2, True),
                 ("?,", 1, "p1", "Value", 1, True),
                 ("$value", 0, "value", "Value", 1, True)]
        tokens = semantic_tokens(server, uri)
        for spelling, occurrence, name, type_name, number, colored in cases:
            start = position(source, spelling, occurrence)
            token = spelling.removesuffix(",")
            result = hover(server, uri, start)
            contents = result["contents"]
            assert isinstance(contents, dict) and isinstance(contents["value"], str), result
            text = contents["value"]
            assert name in text and type_name in text, text
            assert f"SQL parameter `{token}`" in text, text
            assert f"SQLite parameter number {number}." in text, text
            end = {**start, "character": start["character"] + len(token)}
            assert result["range"] == {"start": start, "end": end}, result
            if colored:
                assert (start["line"], start["character"], len(token), "variable") in tokens, tokens
        for token, name in (("$amount", "amount"), ("$greeting", "greeting"), ("$next", "next")):
            target = position(source, name)
            links = server.request("textDocument/definition", {"textDocument": {"uri": uri},
                                   "position": position(source, token)})
            assert isinstance(links, list) and len(links) == 1 and isinstance(links[0], dict), links
            assert links[0]["targetUri"] == uri, links
            assert links[0]["targetSelectionRange"] == {
                "start": target, "end": {**target, "character": target["character"] + len(name)}}, links
        keyword = position(source, "SELECT")
        assert not any(line == keyword["line"] and column == keyword["character"]
                       for line, column, _, _ in tokens), tokens
        escaped = position(source, ":hidden")
        result = hover(server, uri, escaped)
        assert "SQL parameter" not in str(result), result
        assert not any(line == escaped["line"] and column == escaped["character"]
                       for line, column, _, _ in tokens), tokens
        diagnostics = [message for message in server.notifications
                       if message.get("method") == "textDocument/publishDiagnostics"]
        for message in diagnostics:
            params = message["params"]
            assert isinstance(params, dict) and isinstance(params["diagnostics"], list), message
            assert not params["diagnostics"], message
    finally:
        server.close()
