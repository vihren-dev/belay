"""Query, key, alias and conflict mutants detect changed model rules through authored cases.

Each measurement records its targets with native SQLite, requires the base model to agree,
and checks that every mutant changes a verdict. The general Nix owner also contains resolver
and rebuild measurements. Other mutant files have separate scheduled owners because the
combined general suite exceeded its 2,700-second hosted limit. The ownership inventory is
`tests/nix_suites.json`; all owners retain the same harness and deadlines.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from conformance import (algorithm_mutants, alias_mutants, authored_algorithms, authored_aliases,
                         authored_keys, authored_queries, authored_upserts, key_mutants,
                         query_mutants, upsert_mutants)
from conformance.mutation_edits import source_edits
from tests.mutant_sets import Mutants, Targets, measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]


def query_mutant_table(selected: Callable[[str], bool]) -> tuple[Mutants, Targets]:
    """The query mutants of `conformance.query_mutants` whose edited model file satisfies
    `selected`, with their targets: three measurements, each within the time limit."""
    mutants = {name: mutant for name, mutant in query_mutants.MUTANTS.items()
               if selected(source_edits(mutant)[0][0])}
    return mutants, {name: query_mutants.TARGETS[name] for name in mutants}


def is_resolution_file(path: str) -> bool:
    """Whether a query mutant edits a file of the resolution of names and clauses."""
    return path.startswith(query_mutants.SQLITE + "Resolution/")


def test_every_comparison_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query cases notice every changed rule of the comparison of two values
    (the mutants of `conformance.query_mutants` in `Comparison.lean`)."""
    measure_set(runtime_root, [authored_queries],
                [query_mutant_table(lambda path: path == query_mutants.COMPARISON)])


def test_every_query_evaluation_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query cases notice every changed rule of ordering, aggregates, `LIMIT` and
    `OFFSET` (the mutants of `conformance.query_mutants` in `QueryEval.lean` and
    `QueryResults.lean`)."""
    measure_set(runtime_root, [authored_queries],
                [query_mutant_table(lambda path: path != query_mutants.COMPARISON and not is_resolution_file(path))])


def test_every_query_resolution_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query cases notice every removed prepare error of the resolution of
    queries (the mutants of `conformance.query_mutants` in the `Resolution` folder of the
    model)."""
    measure_set(runtime_root, [authored_queries], [query_mutant_table(is_resolution_file)])


def test_every_key_and_alias_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored key and rowid alias cases notice every changed rule of unique key values and
    rowid aliases (`conformance.key_mutants`, `conformance.alias_mutants`)."""
    measure_set(runtime_root, [authored_keys, authored_aliases],
                [(key_mutants.MUTANTS, key_mutants.TARGETS), (alias_mutants.MUTANTS, alias_mutants.TARGETS)])


def test_every_upsert_and_algorithm_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored UPSERT and conflict algorithm cases notice every changed rule of conflict
    handling (`conformance.upsert_mutants`, `conformance.algorithm_mutants`)."""
    measure_set(runtime_root, [authored_upserts, authored_algorithms],
                [(upsert_mutants.MUTANTS, upsert_mutants.TARGETS),
                 (algorithm_mutants.MUTANTS, algorithm_mutants.TARGETS)])
