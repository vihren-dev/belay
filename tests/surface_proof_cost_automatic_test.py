"""S7 proof-cost collector next to the S5 automatic SQL check: the check keeps its result and its cost stays out of the records."""

import pytest

from tests.proof_cost_support import COLLECTOR_IMPORT, Compiler, compiler, compiler_output, counts, runtime_modules  # noqa: F401

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

STATEMENTS = '''
def one := sql "SELECT 1"
theorem rejected (db : Database) : Empty one db := by sorry
theorem proved (db : Database) : Empty one db → Empty one db := fun claim => claim
'''
"""One false statement, which the automatic check rejects, and one true statement, which it accepts
after a search that costs far more than the proof."""


def source(option: str) -> str:
    """The statements, compiled with the collector's option set to `option`."""
    return (COLLECTOR_IMPORT + "import ProofCostReader\nimport Belay\nopen Belay.Sqlite\n"
            f"set_option belay.proofCosts {option}\n" + STATEMENTS + "#proof_cost_records\n")


def test_automatic_check_gives_the_same_result_with_collection(compiler: Compiler) -> None:
    """The collector's handlers leave the S5 linter (`automaticLinter`) its errors and suggestions, and
    the time the linter spends is not in the record of the proof it checks."""
    measured = compiler.compile("Automatic", source("true"), automatic_check=True)
    control = compiler.compile("Automatic", source("false"), automatic_check=True)
    unchecked = compiler.compile("Automatic", source("true"), automatic_check=False)
    assert measured.returncode != 0 and control.returncode != 0, measured.diagnostic()
    assert measured.stdout.count("error: SQL check: false.") == 1, measured.diagnostic()
    assert "Add as a regression example:" in measured.stdout or "Add checked proof example:" in measured.stdout
    assert compiler_output(measured) == compiler_output(control)
    on, off = counts(measured)["proved"], counts(unchecked)["proved"]
    assert abs(on - off) <= max(off, 1000), (on, off)
