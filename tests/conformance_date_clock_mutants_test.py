"""Date and clock mutants detect changed model rules through authored native cases.

The `dateClockMutants` owner separates date inputs, results and modifier rules after
hosted timing exhausted the unchanged 300-second test limit. Every group retains
the native and unchanged-model agreement checks in `measure_set`.
"""

from pathlib import Path

import pytest

from conformance import (authored_clock, authored_date_functions, authored_date_modifiers,
                         clock_mutants, date_function_mutants, date_modifier_mutants)
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]

DATE_INPUT_GUARDS = {"rule:Expr.evaluate", "rule:parseTimezone", "rule:DateTime.ofRawNumber"}
"""Time values, zones and numeric input are measured separately from result formatting."""


def test_every_clock_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored clock cases notice every changed rule of the clock
    (`conformance.clock_mutants`)."""
    measure_set(runtime_root, [authored_clock], [(clock_mutants.MUTANTS, clock_mutants.TARGETS)])


@pytest.mark.parametrize("inputs", [True, False], ids=["inputs", "results"])
def test_every_date_function_mutant_changes_a_verdict(runtime_root: Path, inputs: bool) -> None:
    """The authored date function cases notice every changed input and result rule
    (`conformance.date_function_mutants`) in separate measurements."""
    selected = {name: mutant for name, mutant in date_function_mutants.MUTANTS.items()
                if (date_function_mutants.GUARDS[name] in DATE_INPUT_GUARDS) == inputs}
    measure_set(runtime_root, [authored_date_functions],
                [(selected, {name: date_function_mutants.TARGETS[name] for name in selected})])


@pytest.mark.parametrize("keywords", [False, True], ids=["arithmetic-and-order", "keywords"])
def test_every_date_modifier_mutant_changes_a_verdict(runtime_root: Path, keywords: bool) -> None:
    """The authored modifier cases notice every changed rule of modifier arithmetic, order
    and keywords (`conformance.date_modifier_mutants`) in separate measurements."""
    selected = {name: mutant for name, mutant in date_modifier_mutants.MUTANTS.items()
                if (mutant[0] == date_modifier_mutants.MODIFIER) == keywords}
    measure_set(runtime_root, [authored_date_modifiers],
                [(selected, {name: date_modifier_mutants.TARGETS[name] for name in selected})])
