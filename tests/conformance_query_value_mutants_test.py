"""Number, FROMless, JSON and date mutants detect changed model rules through authored cases.

These measurements use the existing native and base-model agreement checks in `measure_set`.
Their `valueMutants` Nix owner keeps them out of the general suite that exceeded its hosted
limit. Arithmetic has two disjoint measurements after the combined macOS test timed out;
all per-test, subprocess and suite deadlines remain unchanged.
"""

from pathlib import Path

import pytest

from conformance import (authored_clock, authored_date_functions, authored_date_modifiers,
                         authored_fromless, authored_json, authored_json_each, authored_json_functions,
                         authored_numbers, clock_mutants, date_function_mutants, date_modifier_mutants,
                         fromless_mutants, json_each_mutants, json_function_mutants, json_mutants,
                         number_mutants)
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


def test_every_other_number_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored number cases notice every changed rule of sums and averages, number text,
    and `coalesce` (the other mutants of `conformance.number_mutants`)."""
    measure_set(runtime_root, [authored_numbers], [number_mutant_table(False)])


def test_every_fromless_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query-without-FROM cases notice every changed rule of queries without FROM
    (`conformance.fromless_mutants`)."""
    measure_set(runtime_root, [authored_fromless], [(fromless_mutants.MUTANTS, fromless_mutants.TARGETS)])


def test_every_json_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored JSON cases notice every changed rule of JSON reading and `json_extract`
    (`conformance.json_mutants`)."""
    measure_set(runtime_root, [authored_json], [(json_mutants.MUTANTS, json_mutants.TARGETS)])


def test_every_json_function_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored JSON function cases notice every changed rule of `json_type`, `json_valid`,
    `json_array_length` and `json` (`conformance.json_function_mutants`)."""
    measure_set(runtime_root, [authored_json_functions],
                [(json_function_mutants.MUTANTS, json_function_mutants.TARGETS)])


def test_every_json_each_and_clock_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored `json_each` and clock cases notice every changed rule of `json_each` and the
    clock (`conformance.json_each_mutants`, `conformance.clock_mutants`)."""
    measure_set(runtime_root, [authored_json_each, authored_clock],
                [(json_each_mutants.MUTANTS, json_each_mutants.TARGETS),
                 (clock_mutants.MUTANTS, clock_mutants.TARGETS)])


def test_every_date_function_and_modifier_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored date and time function and modifier cases notice every changed rule of
    the date and time functions and their modifiers (`conformance.date_function_mutants`,
    `conformance.date_modifier_mutants`), so these rules are tested."""
    measure_set(runtime_root, [authored_date_functions, authored_date_modifiers],
                [(date_function_mutants.MUTANTS, date_function_mutants.TARGETS),
                 (date_modifier_mutants.MUTANTS, date_modifier_mutants.TARGETS)])


