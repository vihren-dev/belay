"""The measurement of mutant tables over authored cases, shared by the mutant tests.

`tests/conformance_query_mutants_test.py` and `tests/conformance_table_mutants_test.py` run in
two Nix suites, `mutants` and `tableMutants`, whose sources contain only their own test files
and their inputs. This module is an input of both, so neither test file imports the other.
"""

from pathlib import Path
from types import ModuleType

from conformance.native_replay import prepare
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

ROOT = Path(__file__).resolve().parents[1]
"""The repository root, which holds the packages that each mutant copies."""


Mutants = dict[str, tuple[str, str, str]]
"""A mutant table: the file, the exact text and the replacement of each mutant."""
Targets = dict[str, tuple[str, ...]]
"""The target cases of each mutant."""


def measure_set(runtime_root: Path, modules: list[ModuleType], tables: list[tuple[Mutants, Targets]]) -> None:
    """Every target case of the mutant tables, recorded natively from the case modules, agrees
    with the unchanged model, and every mutant changes the verdict of its target case. Only the
    target cases are recorded and classified: the coverage test kernel-checks every case."""
    mutants: Mutants = {}
    targets: Targets = {}
    for table, table_targets in tables:
        assert not set(table) & set(mutants), "mutant names must be unique"
        mutants |= table
        targets |= table_targets
    wanted = {name for names in targets.values() for name in names}
    library = runtime_library(runtime_root)
    cases = []
    for module in modules:
        for record in module.records([case for case in module.definitions() if case.name in wanted]):
            case, answer = prepare(record, library)
            assert case is not None, (record["name"], answer)
            cases.append(case)
    result = measure(cases, ROOT, runtime_root, mutants, targets)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
