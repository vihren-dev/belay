"""Query-resolution mutants detect removed prepare errors through authored queries.

The resolver owner contains this measurement so the query and resolver owners each stay
within their aggregate limit after comparison, evaluation, key and conflict groups split.
"""

from pathlib import Path

import pytest

from conformance import authored_queries, query_mutants
from conformance.mutation_edits import source_edits
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]


def test_every_query_resolution_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query cases notice every removed prepare error of the resolution of
    queries (the mutants of `conformance.query_mutants` in the `Resolution` folder of the
    model)."""
    selected = {name: mutant for name, mutant in query_mutants.MUTANTS.items()
                if source_edits(mutant)[0][0].startswith(query_mutants.SQLITE + "Resolution/")}
    measure_set(runtime_root, [authored_queries],
                [(selected, {name: query_mutants.TARGETS[name] for name in selected})])
