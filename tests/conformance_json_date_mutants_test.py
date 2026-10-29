"""JSON, date and clock mutants detect changed model rules through authored cases.

The `jsonDateMutants` owner retains each exact mutation, native target and base-model check
from the former combined value owner. JSON reading has two semantic groups because its
eight-mutant hosted measurement exceeded the unchanged 300-second test limit. The remaining
tables use semantic groups after their combined measurements left insufficient timing margin.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import (authored_clock, authored_date_functions, authored_date_modifiers,
                         authored_json, authored_json_each, authored_json_functions,
                         clock_mutants, date_function_mutants, date_modifier_mutants,
                         json_each_mutants, json_function_mutants, json_mutants)
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]

JSON_VALUE_GUARDS = {"rule:sqlValueOfNode", "rule:arrowJson", "rule:renderNode"}
"""SQL/JSON values and rendering are measured separately from path lookup and errors."""


@pytest.mark.parametrize("values", [True, False], ids=["values", "lookup-and-errors"])
def test_every_json_mutant_changes_a_verdict(runtime_root: Path, values: bool) -> None:
    """The authored JSON cases notice every changed rule of JSON reading and `json_extract`
    (`conformance.json_mutants`)."""
    selected = {name: mutant for name, mutant in json_mutants.MUTANTS.items()
                if (json_mutants.GUARDS[name] in JSON_VALUE_GUARDS) == values}
    measure_set(runtime_root, [authored_json],
                [(selected, {name: json_mutants.TARGETS[name] for name in selected})])


@pytest.mark.parametrize("validation", [False, True], ids=["functions", "validation"])
def test_every_json_function_mutant_changes_a_verdict(runtime_root: Path, validation: bool) -> None:
    """The authored JSON function cases notice every changed rule of `json_type`, `json_valid`,
    `json_array_length` and `json` (`conformance.json_function_mutants`)."""
    selected = {name: mutant for name, mutant in json_function_mutants.MUTANTS.items()
                if (mutant[0] == json_function_mutants.VALID) == validation}
    measure_set(runtime_root, [authored_json_functions],
                [(selected, {name: json_function_mutants.TARGETS[name] for name in selected})])


@pytest.mark.parametrize(("cases", "table"), [
    pytest.param(authored_json_each, json_each_mutants, id="json-each"),
    pytest.param(authored_clock, clock_mutants, id="clock"),
])
def test_every_json_each_and_clock_mutant_changes_a_verdict(
        runtime_root: Path, cases: ModuleType, table: ModuleType) -> None:
    """The authored `json_each` and clock cases notice every changed rule of `json_each` and the
    clock (`conformance.json_each_mutants`, `conformance.clock_mutants`)."""
    measure_set(runtime_root, [cases], [(table.MUTANTS, table.TARGETS)])


@pytest.mark.parametrize(("cases", "table"), [
    pytest.param(authored_date_functions, date_function_mutants, id="functions"),
    pytest.param(authored_date_modifiers, date_modifier_mutants, id="modifiers"),
])
def test_every_date_function_and_modifier_mutant_changes_a_verdict(
        runtime_root: Path, cases: ModuleType, table: ModuleType) -> None:
    """The authored date and time function and modifier cases notice every changed rule of
    the date and time functions and their modifiers (`conformance.date_function_mutants`,
    `conformance.date_modifier_mutants`), so these rules are tested."""
    measure_set(runtime_root, [cases], [(table.MUTANTS, table.TARGETS)])
