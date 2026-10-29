"""Query, key, alias and conflict mutants detect changed model rules through authored cases.

Each measurement records its targets with native SQLite, requires the base model to agree,
and checks that every mutant changes a verdict. The query owner is separate from query
resolution, resolver and rebuild measurements because the combined suite exceeded its 2,700-second
hosted limit. Comparison and evaluation use semantic groups because comparison approached
the unchanged 300-second test limit and evaluation exceeded it. The ownership inventory is
`tests/nix_suites.json`; all owners retain the same harness and deadlines.
"""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType

import pytest

from conformance import (algorithm_mutants, alias_mutants, authored_algorithms, authored_aliases,
                         authored_keys, authored_queries, authored_upserts, key_mutants,
                         query_mutants, upsert_mutants)
from conformance.mutation_edits import source_edits
from tests.mutant_sets import Mutants, Targets, measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]

AGGREGATE_GUARDS = {"rule:Aggregate.eval", "rule:extremum", "rule:queryGroups"}
"""Aggregate evaluation is measured separately from ordering and windowing."""


def query_mutant_table(selected: Callable[[str], bool]) -> tuple[Mutants, Targets]:
    """The query mutants of `conformance.query_mutants` whose edited model file satisfies
    `selected`, with their original target mappings."""
    mutants = {name: mutant for name, mutant in query_mutants.MUTANTS.items()
               if selected(source_edits(mutant)[0][0])}
    return mutants, {name: query_mutants.TARGETS[name] for name in mutants}


def is_resolution_file(path: str) -> bool:
    """Whether a query mutant edits a file of the resolution of names and clauses."""
    return path.startswith(query_mutants.SQLITE + "Resolution/")


@pytest.mark.parametrize("null_operator", [True, False], ids=["null-operator", "representations"])
def test_every_comparison_mutant_changes_a_verdict(runtime_root: Path, null_operator: bool) -> None:
    """The authored query cases notice every changed rule of the comparison of two values
    (the mutants of `conformance.query_mutants` in `Comparison.lean`)."""
    mutants, targets = query_mutant_table(lambda path: path == query_mutants.COMPARISON)
    selected = {name: mutant for name, mutant in mutants.items()
                if (query_mutants.GUARDS[name] == "rule:Comparison.apply") == null_operator}
    measure_set(runtime_root, [authored_queries], [(selected, {name: targets[name] for name in selected})])


@pytest.mark.parametrize("aggregates", [True, False], ids=["aggregates", "ordering-and-window"])
def test_every_query_evaluation_mutant_changes_a_verdict(runtime_root: Path, aggregates: bool) -> None:
    """The authored query cases notice every changed rule of ordering, aggregates, `LIMIT` and
    `OFFSET` (the mutants of `conformance.query_mutants` in `QueryEval.lean` and
    `QueryResults.lean`)."""
    mutants, targets = query_mutant_table(
        lambda path: path != query_mutants.COMPARISON and not is_resolution_file(path))
    selected = {name: mutant for name, mutant in mutants.items()
                if (query_mutants.GUARDS[name] in AGGREGATE_GUARDS) == aggregates}
    measure_set(runtime_root, [authored_queries], [(selected, {name: targets[name] for name in selected})])


@pytest.mark.parametrize(("cases", "table"), [
    pytest.param(authored_keys, key_mutants, id="keys"),
    pytest.param(authored_aliases, alias_mutants, id="aliases"),
])
def test_every_key_and_alias_mutant_changes_a_verdict(
        runtime_root: Path, cases: ModuleType, table: ModuleType) -> None:
    """The authored key and rowid alias cases notice every changed rule of unique key values and
    rowid aliases (`conformance.key_mutants`, `conformance.alias_mutants`)."""
    measure_set(runtime_root, [cases], [(table.MUTANTS, table.TARGETS)])


@pytest.mark.parametrize(("cases", "table"), [
    pytest.param(authored_upserts, upsert_mutants, id="upsert"),
    pytest.param(authored_algorithms, algorithm_mutants, id="algorithms"),
])
def test_every_upsert_and_algorithm_mutant_changes_a_verdict(
        runtime_root: Path, cases: ModuleType, table: ModuleType) -> None:
    """The authored UPSERT and conflict algorithm cases notice every changed rule of conflict
    handling (`conformance.upsert_mutants`, `conformance.algorithm_mutants`)."""
    measure_set(runtime_root, [cases], [(table.MUTANTS, table.TARGETS)])
