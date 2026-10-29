"""Number and FROMless mutants detect changed model rules through authored cases.

These measurements use the native and base-model agreement checks in `measure_set`.
The `valueMutants` owner keeps numeric work separate from JSON/date/clock work. Arithmetic
and the other number rules use semantic groups after hosted timing showed that
larger groups exceeded or nearly exhausted the unchanged 300-second test limit.
"""

from pathlib import Path

import pytest

from conformance import authored_fromless, authored_numbers, fromless_mutants, number_mutants
from tests.mutant_sets import Mutants, Targets, measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]

REAL_ARITHMETIC_GUARDS = {"rule:ArithmeticOperator.real", "rule:realValue"}
"""Real arithmetic is measured separately from integer arithmetic and CAST."""


def number_mutant_table(arithmetic: bool) -> tuple[Mutants, Targets]:
    """The number mutants of `conformance.number_mutants` in `Arithmetic.lean`, or the others,
    with their targets; arithmetic is divided again by its existing rule guards."""
    mutants = {name: mutant for name, mutant in number_mutants.MUTANTS.items()
               if (mutant[0] == number_mutants.ARITHMETIC) == arithmetic}
    return mutants, {name: number_mutants.TARGETS[name] for name in mutants}


@pytest.mark.parametrize("real", [False, True], ids=["integer-and-cast", "real"])
def test_every_arithmetic_mutant_changes_a_verdict(runtime_root: Path, real: bool) -> None:
    """The authored number cases notice every changed rule of arithmetic and `CAST` to INTEGER
    (`conformance.number_mutants` in `Arithmetic.lean`), in two disjoint measurements."""
    mutants, targets = number_mutant_table(True)
    selected = {name: mutant for name, mutant in mutants.items()
                if (number_mutants.GUARDS[name] in REAL_ARITHMETIC_GUARDS) == real}
    measure_set(runtime_root, [authored_numbers], [(selected, {name: targets[name] for name in selected})])


@pytest.mark.parametrize("source", [number_mutants.SUMMATION, number_mutants.NUMBER_TEXT, None],
                         ids=["summation", "text", "coalesce"])
def test_every_other_number_mutant_changes_a_verdict(runtime_root: Path, source: str | None) -> None:
    """The authored number cases notice every changed rule of sums and averages, number text,
    and `coalesce` (the other mutants of `conformance.number_mutants`)."""
    mutants, targets = number_mutant_table(False)
    separate_sources = (number_mutants.SUMMATION, number_mutants.NUMBER_TEXT)
    selected = {name: mutant for name, mutant in mutants.items()
                if (mutant[0] if mutant[0] in separate_sources else None) == source}
    measure_set(runtime_root, [authored_numbers], [(selected, {name: targets[name] for name in selected})])


def test_every_fromless_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query-without-FROM cases notice every changed rule of queries without FROM
    (`conformance.fromless_mutants`)."""
    measure_set(runtime_root, [authored_fromless], [(fromless_mutants.MUTANTS, fromless_mutants.TARGETS)])
