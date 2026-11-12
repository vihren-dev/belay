"""The derived-column laws of ADR 0017, S6, apply to the guide's lookup claim and to other derived expressions."""

from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import LOWERCASE_LIBRARY, check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_guide_lookup_is_preserved_for_every_database_of_a_site(runtime_root: Path, tmp_path: Path) -> None:
    """Fixture S6RulesQuerySites proves the guide's migration query claim of S6RulesQueryPattern for every
    valid database that has the table, its id column and its name column and no column of the new name, for
    every bound value, and in every complete environment where the migration succeeds. The proof applies the
    general derived-column laws to the lowercase migration. The claim for the one-item database of
    S6RulesQueryPattern is an instance. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        *LOWERCASE_LIBRARY[:4], ("S6RulesQueryPattern", 8), ("S6ColumnLookups", 0), ("S6RulesQuerySites", 6)))


def test_derived_column_law_with_a_schema_premise(runtime_root: Path, tmp_path: Path) -> None:
    """Fixture DerivedColumnSchemaPremise applies the general derived-column law of the package
    (`DerivedColumnMigration.queryPreserves`) to a migration that adds a lowercase column, with the catalog
    of a schema as the premise of the claims, the form that the skill `skills/belay` tells an agent to
    state. The fixture gives the site of the law for every database of the premise and proves that two
    reads keep their results. It also keeps the counterexample of the read with `SELECT *`. Every theorem
    uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("DerivedColumnSchemaPremise", 4),))


def test_boundaries_of_the_computed_derived_column_check(runtime_root: Path, tmp_path: Path) -> None:
    """Fixture DerivedColumnCheckBoundaries checks the boundaries of the computed check
    `DerivedColumnMigration.preservesCheck` of the package: the kernel evaluates it to false for a read with
    `SELECT *`, a column name that exists, a value with a parameter or the clock, a new column with a
    constraint and a trigger that the UPDATE fires. On a second schema, whose migrated table is not the
    first, the check proves a read with an INTEGER filter for every bound value. The theorem uses only
    logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("DerivedColumnCheckBoundaries", 1),), timeout=60)


def test_success_of_the_derived_column_migration_from_the_computed_check(runtime_root: Path, tmp_path: Path) -> None:
    """Fixture DerivedColumnSuccessBoundaries checks the success law `DerivedColumnMigration.succeeds_of_check`
    and its check `succeedsCheck` of the package: the check proves the success of the migration on two schemas
    with only logical axioms, and it is false for a new INTEGER column of a STRICT table and for a value with a
    fallible call. `#sql_check` finds a database on which the STRICT migration fails, so the boundary is real."""
    output = check_module_chain(runtime_root, tmp_path, (("DerivedColumnSuccessBoundaries", 2),), timeout=60)
    assert "SQL check: false." in output, output
    assert "UPDATE customers SET n = email" in output, output


@pytest.mark.requires_native("sqlite3")
def test_other_derived_expressions_and_the_failing_affinity_premise(runtime_root: Path, tmp_path: Path) -> None:
    """The general laws apply to the concatenation of two columns stored in a TEXT column (fixtures
    ConcatFilters, ConcatExpansion and DerivedColumnExamples), and an integer sum stored in a TEXT column
    with a REAL probe is a case where the affinity premise fails and the moved lookup finds nothing. Pinned
    SQLite 3.51.0 gives the rows that the kernel gives for the original and the moved lookups of both
    examples. Every theorem uses only logical axioms."""
    stdout = check_module_chain(runtime_root, tmp_path, (
        *LOWERCASE_LIBRARY[:3], ("ConcatFilters", 0), ("ConcatExpansion", 0), ("DerivedColumnExamples", 9)))
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = {str(report["name"]): report for report in lines_after(stdout, "REPLAY:") if isinstance(report, dict)}
    assert set(reports) == {"joined-before", "joined-after", "summed-before", "summed-after"}, stdout
    expected_rows = {"joined-before": [[1]], "joined-after": [[1]], "summed-before": [[1]], "summed-after": []}
    for name, report in reports.items():
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        assert result.returncode == 0 and not result.stderr, result.diagnostic()
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        modeled = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
        assert native_rows(result.stdout) == modeled == expected_rows[name], (name, result.stdout, modeled)
