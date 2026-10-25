"""Actual document edits cancel the active SQL linter through Lean's native token."""

from collections.abc import Callable
import json
from pathlib import Path
import time

import pytest

from tests.lean_server_support import LeanServer
from tests.surface_automatic_editor_test import diagnostics

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.parametrize("edit", ["earlier command", "same command"])
def test_automatic_document_cancellation(edit: str, runtime_root: Path, tmp_path: Path,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """SqlAutomatic runs with the server cancellation context. A test-only wrapper observes
    entry with a live token and the actual linter's interruption. The edited document completes
    without a stale false-claim diagnostic or suggestion, and no replacement checker runs.

    Lean 4.34.1 sets the linter token only when a command before the checked statement changes
    (`Language/Lean.lean` parseCmd cancels the later commands of the old document). Editing the
    statement itself discards the obsolete snapshot and its diagnostics, but Lean leaves the old
    linter running until it finishes or `sql.checkBudget` stops it, so only the first case may
    require an interrupt."""
    entered = tmp_path / "entered"
    cancelled = tmp_path / "cancelled"
    finished = tmp_path / "finished"
    source = f'''import Belay
open Belay.Sqlite Lean Elab
run_elab
  Command.lintersRef.modify fun linters => linters.map fun linter =>
    if linter.name != `Belay.Sqlite.Check.automaticLinter then linter else
    {{ linter with run := fun command => do
      if !(command.find? fun node => node.isOfKind ``Parser.Command.theorem &&
          node[1][0].isIdent && node[1][0].getId == `longCheck).isSome then
        return ← linter.run command
      let some token := (← read).cancelTk? | throwError "missing native cancellation token"
      if ← token.isSet then throwError "checker was cancelled before entry"
      IO.FS.writeFile {json.dumps(str(entered))} s!"{{← IO.monoMsNow}}"
      let observed : Command.CommandElabM Unit := fun context state => do
        match ← (linter.run command context state).toBaseIO with
        | .ok result => pure result
        | .error error =>
          IO.toEIO (fun failure => Exception.error command m!"{{failure}}") do
            IO.FS.writeFile {json.dumps(str(finished))}
              s!"time={{← IO.monoMsNow}} interrupt={{error.isInterrupt}} cancelled={{← token.isSet}}: {{← error.toMessageData.toString}}"
            if error.isInterrupt then
              IO.FS.writeFile {json.dumps(str(cancelled))} "interrupted"
          throw error
      observed
      IO.FS.writeFile {json.dumps(str(finished))}
        s!"time={{← IO.monoMsNow}} completed normally cancelled={{← token.isSet}}" }}
def one := sql "SELECT 1"
set_option sql.checkBudget 1000000
'''
    original = source + "theorem longCheck (db : Database) : Empty one db := by sorry\n"
    replacement = (source.replace("1000000", "1000001") if edit == "earlier command" else source
                   ) + "theorem replacement : True := by trivial\n"
    server = LeanServer(runtime_root, tmp_path, automatic_check=True)
    try:
        uri = server.open(original, wait=False)
        deadline = time.monotonic() + 30
        while not entered.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        if not entered.exists():
            pytest.fail(f"Checker did not start: {diagnostics(server, uri, 1)}")
        assert entered.read_text().isdigit()
        start = time.monotonic()
        server.send({"method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": replacement}]}})
        reports = diagnostics(server, uri, 2)
        record_testsuite_property("automatic.cancellation.seconds", time.monotonic() - start)
        deadline = time.monotonic() + 30
        while not finished.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        if edit == "earlier command":
            assert cancelled.exists(), (finished.read_text() if finished.exists() else "checker still active", reports)
            assert cancelled.read_text() == "interrupted", reports
            assert "interrupt=true" in finished.read_text(), finished.read_text()
        assert not reports, reports
        updates = [message["params"] for message in server.notifications
                   if message.get("method") == "textDocument/publishDiagnostics"]
        assert not any("SQL check: false." in str(update) for update in updates), updates
        actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
            "range": {"start": {"line": len(source.splitlines()), "character": 8},
                      "end": {"line": len(source.splitlines()), "character": 19}},
            "context": {"diagnostics": []}})
        assert not actions, actions
    finally:
        server.close()
