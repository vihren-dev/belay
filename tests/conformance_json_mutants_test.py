"""JSON mutants detect changed model rules through authored native cases.

The `jsonMutants` owner measures conversion, rendering and lookup/error rules separately
after hosted timing left insufficient margin within the unchanged 300-second test limit.
Every group retains the native and unchanged-model agreement checks in `measure_set`.
"""

from pathlib import Path

import pytest

from conformance import (authored_json, authored_json_each, authored_json_functions,
                         json_each_mutants, json_function_mutants, json_mutants)
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]

JSON_VALUE_GROUPS = {"rule:sqlValueOfNode": "conversion", "rule:arrowJson": "conversion",
                     "rule:renderNode": "rendering"}
"""Value conversion and rendering guards; the other guards cover lookup and errors."""


@pytest.mark.parametrize("group", ["conversion", "rendering", "lookup-and-errors"])
def test_every_json_mutant_changes_a_verdict(runtime_root: Path, group: str) -> None:
    """The authored JSON cases notice every changed rule of JSON reading and `json_extract`
    (`conformance.json_mutants`)."""
    selected = {name: mutant for name, mutant in json_mutants.MUTANTS.items()
                if JSON_VALUE_GROUPS.get(json_mutants.GUARDS[name], "lookup-and-errors") == group}
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


def test_every_json_each_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored `json_each` cases notice every changed rule of `json_each`
    (`conformance.json_each_mutants`)."""
    measure_set(runtime_root, [authored_json_each], [(json_each_mutants.MUTANTS, json_each_mutants.TARGETS)])
