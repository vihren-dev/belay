"""Default statement checks use completed propositions and exclude proof-body evidence."""

from collections.abc import Callable
from pathlib import Path
import time

import pytest

from tests.runtime_support import run_command
from tests.surface_support import surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

PRELUDE = 'import Belay\nopen Belay.Sqlite\ndef one := sql "SELECT 1"\n'
"""One supported query shared by statements; the original theorem is never an artifact premise."""

CASES: dict[str, tuple[str, int, int]] = {
    "named": ("theorem rejected (db : Database) : Empty one db := by sorry\n", 1, 1),
    "anonymous": ("example : ∀ db, Empty one db := by sorry\n", 1, 1),
    "anonymous-local": ("example : ∀ db, Empty one db := by\n"
                        "  have claimed : ∀ db, Empty one db := by sorry\n  exact claimed\n", 1, 1),
    "proof-valued-definition": ("def uncheckedDefinition : ∀ db, Empty one db := by sorry\n", 0, 0),
    "body-local": ("theorem rejected : ∀ db, Empty one db := by\n"
                   "  have claimed : ∀ db, Empty one db := by sorry\n  exact claimed\n", 1, 1),
    "mutual": ("set_option sql.checkBudget 200000 in\nmutual\n  theorem firstPeer (db : Database) : Empty one db := by exact secondPeer db\n"
               "  theorem secondPeer (db : Database) : Empty one db := by sorry\nend\n", 2, 2),
    "section": ("section\nvariable (db : Database) (premise : Empty one db)\ninclude premise\n"
                "theorem fromSection : Empty one db := premise\nend\n", 0, 1),
    "proved": ("theorem proved (db : Database) : Empty one db → Empty one db := by sorry\n", 0, 1),
    "unrelated": ("theorem unrelated : 0 = 1 := by sorry\n", 0, 0),
    "disabled": ("set_option sql.check false in\n"
                 "theorem disabled (db : Database) : Empty one db := by sorry\n", 0, 0),
    "budget": ("set_option sql.checkBudget 1 in\n"
               "theorem bounded (db : Database) : Empty one db := by sorry\n", 0, 0),
}
"""Expected false-claim errors and independently checked example suggestions for each boundary."""


@pytest.mark.parametrize("case", CASES)
def test_automatic_statement_boundaries(runtime_root: Path, tmp_path: Path, case: str,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """SqlAutomatic checks original named/anonymous/mutual statements, keeps section premises,
    rejects proof-body assumptions, and leaves unrelated/disabled/exhausted claims alone."""
    body, errors, suggestions = CASES[case]
    source = tmp_path / "Automatic.lean"
    source.write_text(PRELUDE + body)
    start = time.monotonic()
    result = run_command(surface_command(runtime_root, source, tmp_path, automatic_check=True), cwd=tmp_path, timeout=120)
    record_testsuite_property(f"sql_automatic.{case}.elapsed_seconds", time.monotonic() - start)
    assert (result.returncode != 0) == (errors > 0), result.diagnostic()
    assert result.stdout.count("error: SQL check: false.") == errors, result.diagnostic()
    assert result.stdout.count("Add as a regression example:") + result.stdout.count(
        "Add checked proof example:") == suggestions, result.diagnostic()
    assert "linter Belay.Sqlite.Check.automaticLinter failed" not in result.stdout, result.diagnostic()
    assert "maximum recursion depth" not in result.stdout, result.diagnostic()
