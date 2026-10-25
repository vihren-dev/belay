"""Native editor diagnostics and checked append actions for SQL theorem statements."""

from collections.abc import Callable
from pathlib import Path
import shutil
import re
import time

import pytest

from tests.lean_server_support import LeanServer
from tests.runtime_support import run_command
from tests.surface_execution_test import ALLOWED_PROOF_AXIOMS
from tests.surface_editor_test import position
from tests.surface_replay_test import native_replay, native_rows
from tests.surface_support import surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

PRELUDE = '''import Belay
open Belay.Sqlite
def one := sql "SELECT 1"
def parameterized (env : Value) := sql "SELECT $env"
'''
"""Both source queries are retained when the artifact is checked without the original theorem."""

CASES: dict[str, tuple[str, str, bool]] = {
    "false": ("/- 😀 -/ theorem rejected (db : Database) : Empty one db := by sorry", "rejected", True),
    "parameter": ("theorem rejected (env : Value) (db : Database) : Empty (parameterized env) db := by sorry",
                  "rejected", True),
    "proof": ("theorem sound (kernel : Nat) (db : Database) : Empty one db → Empty one db := by exact id",
              "sound", False),
    "section": ("section\nvariable (db : Database) (premise : Empty one db)\ninclude premise\n"
                "theorem fromSection : Empty one db := premise\nend", "fromSection", False),
    "mutual": ("set_option sql.checkBudget 200000 in\nmutual\n"
               "  theorem firstPeer (db : Database) : Empty one db := by exact secondPeer db\n"
               "  theorem secondPeer (db : Database) : Empty one db := by sorry\nend", "firstPeer", True),
}
"""Capture, original-context and mutual-peer boundaries of independently usable examples."""


def diagnostics(server: LeanServer, uri: str, version: int) -> list[dict[str, object]]:
    """Wait for completed background linters and select the last diagnostics for this version."""
    server.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version}, timeout=90)
    reports = [message["params"] for message in server.notifications
               if message.get("method") == "textDocument/publishDiagnostics"
               and message["params"].get("uri") == uri and message["params"].get("version") == version]
    assert reports, server.notifications
    return reports[-1]["diagnostics"]


def offset(source: str, point: dict[str, int]) -> int:
    """Convert a native UTF-16 edit position to a Python string offset, retaining CRLF."""
    lines = source.splitlines(keepends=True)
    prefix = "".join(lines[:point["line"]])
    line = lines[point["line"]] if point["line"] < len(lines) else ""
    text = line.encode("utf-16-le")[:point["character"] * 2].decode("utf-16-le")
    return len(prefix) + len(text)


@pytest.mark.requires_native("sqlite3")
@pytest.mark.parametrize(("case", "newline"), [("false", "\n"), ("false", "\r\n"),
    ("parameter", "\n"), ("proof", "\n"), ("section", "\n"), ("mutual", "\n")])
def test_automatic_editor_actions(runtime_root: Path, tmp_path: Path, case: str, newline: str,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """SqlAutomatic uses native statement ranges and actions; exact inserted text checks alone,
    has safe axioms, preserves the original error, and replays the original SQL under SQLite."""
    body, name, refuted = CASES[case]
    source = (PRELUDE + body + "\n").replace("\n", newline)
    server = LeanServer(runtime_root, tmp_path, automatic_check=True)
    try:
        start = time.monotonic()
        uri = server.open(source, wait=False)
        reports = diagnostics(server, uri, 1)
        record_testsuite_property(f"automatic.editor.{case}.{newline!r}.seconds", time.monotonic() - start)
        selection = position(source, name)
        span = {"start": selection, "end": {**selection, "character": selection["character"] + len(name)}}
        errors = [report for report in reports if report.get("severity") == 1]
        assert len(errors) == (2 if case == "mutual" else int(refuted)), reports
        if refuted:
            assert any(report["range"] == span and str(report["message"]).startswith("SQL check: false.")
                       for report in errors), reports
        actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
            "range": span, "context": {"diagnostics": []}})
        title = "Add as a regression example" if refuted else "Add checked proof example"
        matching = [action for action in actions if action.get("title") == title]
        assert len(matching) == 1, actions
        changes = matching[0]["edit"]["documentChanges"]
        assert len(changes) == 1 and changes[0]["textDocument"] == {"uri": uri, "version": 1}, changes
        edits = changes[0]["edits"]
        assert len(edits) == 1 and edits[0]["range"]["start"] == edits[0]["range"]["end"], edits
        artifact = edits[0]["newText"]
        assert "set_option sql.check false in" in artifact, artifact
        if case == "parameter":
            assert re.search(r"\(input\s+env\s*:=", artifact), artifact
        standalone = tmp_path / "Suggested.lean"
        named = artifact.replace("example :", "theorem checkedArtifact :", 1)
        standalone.write_text(PRELUDE + named + "\n#print axioms checkedArtifact\n")
        checked = run_command(surface_command(runtime_root, standalone, tmp_path), cwd=tmp_path, timeout=90)
        assert checked.returncode == 0, checked.diagnostic()
        audit = re.search(r"'checkedArtifact' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                          checked.stdout)
        assert audit is not None, checked.stdout
        dependencies = set(filter(None, map(str.strip, (audit[1] or "").split(","))))
        assert dependencies <= ALLOWED_PROOF_AXIOMS, dependencies
        assert not dependencies.intersection({name, "firstPeer", "secondPeer"}), dependencies
        insertion = offset(source, edits[0]["range"]["start"])
        edited = source[:insertion] + artifact + source[insertion:]
        server.send({"method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": edited}]}})
        edited_reports = diagnostics(server, uri, 2)
        assert [report for report in edited_reports if report.get("severity") == 1] == errors, edited_reports
        if refuted:
            sqlite = shutil.which("sqlite3")
            assert sqlite is not None
            report = next(report for report in errors if report["range"] == span)
            sql = report["message"].split("SQLite replay:\n", 1)[1]
            replay = native_replay(sqlite, sql, tmp_path, case)
            assert replay.returncode == 0 and not replay.stderr, replay.diagnostic()
            assert native_rows(replay.stdout) == ([[None]] if case == "parameter" else [[1]]), replay.diagnostic()
    finally:
        server.close()


def test_automatic_editor_options(runtime_root: Path, tmp_path: Path) -> None:
    """Native editor checks honor local disable/exhaustion controls and preserve ordinary
    elaboration errors; none of these commands emits a false-claim error or an SQL action."""
    source = PRELUDE + '''set_option sql.check false in
theorem disabled (db : Database) : Empty one db := by sorry
set_option sql.checkBudget 1 in
theorem exhausted (db : Database) : Empty one db := by sorry
set_option sql.checkRecursionLimit 1 in
theorem shallow (db : Database) : Empty one db := by sorry
theorem ordinary : 0 = 1 := by rfl
'''
    server = LeanServer(runtime_root, tmp_path, automatic_check=True)
    try:
        uri = server.open(source, wait=False)
        reports = diagnostics(server, uri, 1)
        errors = [report for report in reports if report.get("severity") == 1]
        assert len(errors) == 1 and "rfl" in errors[0]["message"], reports
        assert not any("SQL check: false." in str(report) or "linter" in str(report) for report in errors), reports
        for name in ("disabled", "exhausted", "shallow", "ordinary"):
            point = position(source, name)
            actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
                "range": {"start": point, "end": point}, "context": {"diagnostics": []}})
            assert not any(str(action.get("title", "")).startswith("Add ") for action in actions), actions
    finally:
        server.close()
