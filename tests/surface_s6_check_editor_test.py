"""The automatic check of ADR 0017, S6 on claims about programs: diagnostics, code actions and cancellation."""

from pathlib import Path
import re
import shutil
import json
import time

import pytest

from tests.lean_server_support import LeanServer, compile_helper_module, position
from tests.runtime_support import run_command
from tests.surface_automatic_editor_test import diagnostics, offset
from tests.surface_execution_test import ALLOWED_PROOF_AXIOMS
from tests.surface_replay_test import native_replay, native_rows
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

HEADER = '''import S6RulesEffects
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
'''
"""The imports, options and namespaces of every document. A suggested example must keep them."""

CLAIM = '''FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer {quantity}]]⌝ : ContextAssertion))'''
"""The claim that the update of `bump` leaves the row with a given quantity. The quantity is 6 after the update."""

DOCUMENT = HEADER + f'''set_option sql.checkBudget 250000 in
theorem wrongRows : {CLAIM.format(quantity=7)} := by sorry
theorem rightRows : {CLAIM.format(quantity=6)} := by sorry
set_option sql.checkBudget 1 in
theorem tooLittleBudget : {CLAIM.format(quantity=7)} := by sorry
end S6RulesEffects
'''
"""Three theorems with the proof `sorry`: a false claim, a true claim, and a false claim with a budget of one unit."""


def action_edit(server: LeanServer, uri: str, name: str, source: str, title: str) -> tuple[str, dict[str, object]]:
    """The text that the one code action of the given title inserts at the theorem, with its range."""
    selection = position(source, name)
    span = {"start": selection, "end": {**selection, "character": selection["character"] + len(name)}}
    actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
        "range": span, "context": {"diagnostics": []}})
    matching = [action for action in actions if action.get("title") == title]
    assert len(matching) == 1, actions
    [change] = matching[0]["edit"]["documentChanges"]
    assert change["textDocument"] == {"uri": uri, "version": 1}, change
    [edit] = change["edits"]
    assert edit["range"]["start"] == edit["range"]["end"], edit
    return edit["newText"], edit["range"]


def check_alone(runtime_root: Path, directory: Path, extra: dict[str, list[list[str]]], artifact: str) -> None:
    """Elaborate the suggested example as a theorem of its own and audit its axioms."""
    file = directory / "Suggested.lean"
    named = artifact.replace("example :", "theorem checkedArtifact :", 1)
    file.write_text(HEADER + named + "\n#print axioms checkedArtifact\nend S6RulesEffects\n")
    setup = module_setup(runtime_root, directory, module="Suggested", extra_modules=extra)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}", str(file)],
                         cwd=directory, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    audit = re.search(r"'S6RulesEffects.checkedArtifact' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                      result.stdout)
    assert audit is not None, result.stdout
    assert set(filter(None, map(str.strip, (audit[1] or "").split(",")))) <= ALLOWED_PROOF_AXIOMS, result.stdout


@pytest.mark.requires_native("sqlite3")
def test_automatic_check_reports_and_offers_actions_for_triples(runtime_root: Path, tmp_path: Path) -> None:
    """The automatic check refutes the false triple with a replay that native SQLite confirms (the quantity 6, not
    7), proves the true triple and offers a checked proof example that elaborates alone with ordinary axioms, and
    reports nothing when the budget is one unit: the check is then unknown, and no action appears."""
    extra = compile_helper_module(runtime_root, tmp_path, "S6RulesEffects",
                                  (FIXTURES / "S6RulesEffects.lean").read_text())
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture", extra_modules=extra, automatic_check=True)
    try:
        uri = server.open(DOCUMENT, wait=False)
        reports = diagnostics(server, uri, 1)
        errors = [report for report in reports if report.get("severity") == 1]
        [false_report] = [report for report in errors if str(report["message"]).startswith("SQL check: false.")]
        assert len(errors) == 1, reports
        start = position(DOCUMENT, "wrongRows")
        assert false_report["range"]["start"] == start, false_report
        message = str(false_report["message"])
        assert "Failing observation: The check fails on the actual run of the program." in message, message
        sqlite = shutil.which("sqlite3")
        assert sqlite is not None
        replay = native_replay(sqlite, message.split("SQLite replay:\n", 1)[1], tmp_path, "wrong",
                               inspect="\nSELECT id, qty FROM items;\n")
        assert replay.returncode == 0 and not replay.stderr, replay.diagnostic()
        assert native_rows(replay.stdout) == [[1, 6]], replay.diagnostic()
        regression, _ = action_edit(server, uri, "wrongRows", DOCUMENT, "Add as a regression example")
        assert "set_option sql.check false in" in regression and "sql_refute" in regression, regression
        check_alone(runtime_root, tmp_path, extra, regression)
        proof, range_ = action_edit(server, uri, "rightRows", DOCUMENT, "Add checked proof example")
        assert "sql_run" in proof and "sorry" not in proof, proof
        check_alone(runtime_root, tmp_path, extra, proof)
        silent = position(DOCUMENT, "tooLittleBudget")
        assert not [report for report in reports if report["range"]["start"] == silent
                    and not str(report["message"]).startswith("declaration uses")], reports
        none = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
            "range": {"start": position(DOCUMENT, "tooLittleBudget"), "end": position(DOCUMENT, "tooLittleBudget")},
            "context": {"diagnostics": []}})
        assert not [action for action in none if "example" in str(action.get("title"))], none
        insertion = offset(DOCUMENT, range_["start"])
        edited = DOCUMENT[:insertion] + proof + DOCUMENT[insertion:]
        server.send({"method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": edited}]}})
        edited_reports = diagnostics(server, uri, 2)
        assert [report for report in edited_reports if report.get("severity") == 1] == errors, edited_reports
    finally:
        server.close()


def test_automatic_check_of_an_equivalence_is_cancelled_by_an_edit_of_an_earlier_command(
        runtime_root: Path, tmp_path: Path) -> None:
    """The automatic check of an equivalence between programs runs with the server's cancellation token. A change
    of an earlier command interrupts the running check, the edited document completes without a stale
    false-claim diagnostic, and no replacement check reports."""
    entered, cancelled = tmp_path / "entered", tmp_path / "cancelled"
    extra = compile_helper_module(runtime_root, tmp_path, "S6RulesEffects",
                                  (FIXTURES / "S6RulesEffects.lean").read_text())
    source = HEADER + f'''open Lean Elab in
run_elab
  Command.lintersRef.modify fun linters => linters.map fun linter =>
    if linter.name != `Belay.Sqlite.Check.automaticLinter then linter else
    {{ linter with run := fun command => do
      if !(command.find? fun node => node.isOfKind ``Parser.Command.theorem &&
          node[1][0].isIdent && node[1][0].getId == `longCheck).isSome then
        return ← linter.run command
      let some token := (← read).cancelTk? | throwError "missing native cancellation token"
      IO.FS.writeFile {json.dumps(str(entered))} s!"{{← IO.monoMsNow}}"
      let observed : Command.CommandElabM Unit := fun context state => do
        match ← (linter.run command context state).toBaseIO with
        | .ok result => pure result
        | .error error =>
          IO.toEIO (fun failure => Exception.error command m!"{{failure}}") do
            if error.isInterrupt then IO.FS.writeFile {json.dumps(str(cancelled))} "interrupted"
          throw error
      observed }}
def bumpTwice : Script := sql r"UPDATE items SET qty = qty + 2 WHERE id = ?1" (Value.integer 1)
set_option sql.checkBudget 20000000
'''
    original = source + "theorem longCheck : Sql.Equiv (send bump) (send bumpTwice) := by sorry\nend S6RulesEffects\n"
    replacement = source.replace("20000000", "20000001") + "theorem replacement : True := by trivial\nend S6RulesEffects\n"
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture", extra_modules=extra, automatic_check=True)
    try:
        uri = server.open(original, wait=False)
        deadline = time.monotonic() + 60
        while not entered.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert entered.exists(), diagnostics(server, uri, 1)
        server.send({"method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": replacement}]}})
        reports = diagnostics(server, uri, 2)
        deadline = time.monotonic() + 30
        while not cancelled.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert cancelled.exists() and cancelled.read_text() == "interrupted", reports
        assert not [report for report in reports if report.get("severity") == 1], reports
        updates = [message["params"] for message in server.notifications
                   if message.get("method") == "textDocument/publishDiagnostics"]
        assert not any("SQL check: false." in str(update) for update in updates), updates
    finally:
        server.close()
