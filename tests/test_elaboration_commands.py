"""`migration_check.elaboration_commands`: the commands that `prepare` reports in approved sources."""

import pytest

from migration_check.elaboration_commands import elaboration_commands

pytestmark = pytest.mark.unit


def test_reports_commands_that_run_code_during_elaboration() -> None:
    """`elaboration_commands` names each `#eval`, `run_cmd`, `initialize` and syntax-extension command with its
    module and line, because a cached output of such a module can differ from a fresh one."""
    sources = {"Requirements": b"def x := 1\n#eval x\n@[simp] macro \"m\" : term => `(1)\n",
               "Interpretation": b"private initialize counter : IO.Ref Nat <- IO.mkRef 0\nrun_cmd pure ()\n"}
    assert elaboration_commands(sources) == [
        "Interpretation:1: initialize", "Interpretation:2: run_cmd", "Requirements:2: #eval", "Requirements:3: macro"]


def test_plain_definitions_and_comments_are_not_reported() -> None:
    """`elaboration_commands` reports nothing for definitions, theorems, and keywords inside comments or names."""
    sources = {"Requirements": b"/- #eval in a comment\n#eval still in it -/\ndef evaluate := 1\n"
                               b"theorem macro_free : True := trivial\n-- run_cmd in a line comment\n"}
    assert elaboration_commands(sources) == []
