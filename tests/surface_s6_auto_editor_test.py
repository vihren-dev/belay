"""The editor action of `sql_auto` (ADR 0017, S6): request it, apply it, and check the replacement alone."""

from pathlib import Path
import re

import pytest

from tests.lean_server_support import LeanServer, compile_helper_module, position
from tests.runtime_support import run_command
from tests.surface_automatic_editor_test import diagnostics, offset
from tests.surface_execution_test import ALLOWED_PROOF_AXIOMS
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

TITLE_PREFIX = "Try this:"
"""The title prefix of the code action that `sql_auto` offers; the title adds the new steps."""

HEADER = '''import S6RulesEffects
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
'''
"""The imports, options, namespace and opened namespaces of the document. A replacement must keep them."""

CASES: dict[str, tuple[str, str, str, list[str]]] = {
    "run": ('''theorem editorBump :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_auto [rfl, ⟨_, _, _, rfl⟩]
''', "editorBump", "sql_auto [rfl, ⟨_, _, _, rfl⟩]", ["sql_run [rfl, ⟨_, _, _, rfl⟩]", "· intros; rfl"]),
    "grind": ('''theorem editorGrind (rows : List Nat) (given : rows = [1, 2]) : rows.length = 2 := by
  sql_auto [given]
''', "editorGrind", "sql_auto [given]", ["grind"]),
}
"""Documents with a proof by `sql_auto`: the source, the theorem, the call, and the steps that replace it."""


def check_alone(runtime_root: Path, directory: Path, extra: dict[str, list[list[str]]], source: str,
                name: str) -> None:
    """Elaborate the document with the replacement, and audit the axioms of the theorem."""
    file = directory / "Replaced.lean"
    qualified = f"S6RulesEffects.{name}"
    file.write_text(source + f"\n#print axioms {qualified}\n")
    setup = module_setup(runtime_root, directory, module="Replaced", extra_modules=extra)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}", str(file)],
                         cwd=directory, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    audit = re.search(rf"'{qualified}' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                      result.stdout)
    assert audit is not None, result.stdout
    dependencies = set(filter(None, map(str.strip, (audit[1] or "").split(","))))
    assert dependencies <= ALLOWED_PROOF_AXIOMS, dependencies
    assert "sql_auto" not in source and "Try this" not in result.stdout, result.stdout


@pytest.mark.parametrize("case", sorted(CASES))
def test_sql_auto_action_replaces_the_call_with_its_steps(runtime_root: Path, tmp_path: Path, case: str) -> None:
    """`sql_auto` offers one code action that replaces exactly the call with the explicit steps of the route that
    closed the goal. The edited document keeps the imports, options, namespaces and hypotheses of the original,
    shows no error, offers no second action, and proves the theorem without a search, with ordinary axioms."""
    body, name, call, steps = CASES[case]
    source = HEADER + body + "end S6RulesEffects\n"
    extra = compile_helper_module(runtime_root, tmp_path, "S6RulesEffects",
                                  (FIXTURES / "S6RulesEffects.lean").read_text())
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture", extra_modules=extra)
    try:
        uri = server.open(source, wait=False)
        reports = diagnostics(server, uri, 1)
        assert not [report for report in reports if report.get("severity") == 1], reports
        start = position(source, call)
        span = {"start": start, "end": {**start, "character": start["character"] + len(call)}}
        actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
            "range": span, "context": {"diagnostics": []}})
        matching = [action for action in actions if str(action.get("title", "")).startswith(TITLE_PREFIX)]
        assert len(matching) == 1, actions
        changes = matching[0]["edit"]["documentChanges"]
        assert len(changes) == 1 and changes[0]["textDocument"] == {"uri": uri, "version": 1}, changes
        edits = changes[0]["edits"]
        assert len(edits) == 1 and edits[0]["range"] == span, edits
        replacement = edits[0]["newText"]
        assert [line.strip() for line in replacement.splitlines() if line.strip()] == steps, replacement
        begin, end = offset(source, span["start"]), offset(source, span["end"])
        edited = source[:begin] + replacement + source[end:]
        server.send({"method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": edited}]}})
        edited_reports = diagnostics(server, uri, 2)
        assert not [report for report in edited_reports if report.get("severity") in (1, 2)], edited_reports
        assert not any("Try this" in str(report) for report in edited_reports), edited_reports
        check_alone(runtime_root, tmp_path, extra, edited, name)
    finally:
        server.close()


def test_sql_auto_offers_no_action_when_no_route_closes_the_goal(runtime_root: Path, tmp_path: Path) -> None:
    """A call that no route closes reports one error that names each route, and the document offers no action
    to replace the call, so the editor never suggests an unchecked script."""
    source = HEADER + "theorem editorFalse : (1 : Nat) = 2 := by\n  sql_auto\nend S6RulesEffects\n"
    extra = compile_helper_module(runtime_root, tmp_path, "S6RulesEffects",
                                  (FIXTURES / "S6RulesEffects.lean").read_text())
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture", extra_modules=extra)
    try:
        uri = server.open(source, wait=False)
        reports = diagnostics(server, uri, 1)
        errors = [report for report in reports if report.get("severity") == 1]
        assert len(errors) == 1, reports
        for route in ("sql_commute", "sql_run", "grind"):
            assert f"- {route}:" in str(errors[0]["message"]), errors
        point = position(source, "sql_auto")
        actions = server.request("textDocument/codeAction", {"textDocument": {"uri": uri},
            "range": {"start": point, "end": point}, "context": {"diagnostics": []}})
        assert not any(str(action.get("title", "")).startswith(TITLE_PREFIX) for action in actions), actions
    finally:
        server.close()
