"""Each mutant of the function tables of ADR 0015 changes the verdict of an authored case.

ADR 0015 adds SQL functions slice by slice, and each slice lists the changes of its rules
that the conformance suite must notice. The cases are the authored cases of
`conformance.authored_text_functions` (slice 1) and `conformance.authored_numeric_functions`
(slice 2), recorded natively with their outputs. Each measurement builds one base copy for
its mutants with `measure_set` of `tests/mutant_sets.py`, and each mutant
copy classifies the case that the mutant names as its target.
"""

from pathlib import Path

import pytest

from conformance import authored_numeric_functions, authored_text_functions, function_mutants, numeric_function_mutants
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]


def test_every_text_function_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of the text and type functions notice every changed rule
    (`conformance.function_mutants`): `length` that counts bytes in text, `lower` that changes
    non-ASCII bytes, and `LIKE` that compares case (ADR 0015, slice 1)."""
    measure_set(runtime_root, [authored_text_functions], [(function_mutants.MUTANTS, function_mutants.TARGETS)])


def test_every_numeric_function_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of the exact numeric functions notice every changed rule
    (`conformance.numeric_function_mutants`): `round` that rounds half to even, `floor` that
    truncates toward zero, and `mod` that keeps an integer result (ADR 0015, slice 2)."""
    measure_set(runtime_root, [authored_numeric_functions],
                [(numeric_function_mutants.MUTANTS, numeric_function_mutants.TARGETS)])

