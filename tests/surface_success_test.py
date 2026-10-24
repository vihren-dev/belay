"""S4 program composition and success contracts in the public Lean surface."""

import json
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_program_laws_preserve_connection_and_next_index(runtime_root: Path, tmp_path: Path) -> None:
    """ProgramMonadLaws and ProgramBindLaws compose arbitrary programs, preserve transactions,
    advance a statement-dependent clock, and stop before the next program after an unmodeled step.
    The law wrappers use no unchecked reduction axiom."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessProgramLaws.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 3, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_success_checks_actual_and_alternative_continuations(runtime_root: Path, tmp_path: Path) -> None:
    """Succeeds rejects both a failing LIMIT alternative and a raw continuation that fails only
    on the actual oneOf wrapper; the fixtures also cover clock inputs, random and generic laws."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessBranches.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 4, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_success_notation_checks_its_query_at_the_query(runtime_root: Path, tmp_path: Path) -> None:
    """SuccessSyntax elaborates both forms and bound parameters, and rejects multi-statement
    or writing preconditions at the query's source span."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessSyntaxExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_query_success_keeps_errors_and_ending_outputs(runtime_root: Path, tmp_path: Path) -> None:
    """QuerySuccess proves arbitrary-database success through the query/environment bridge
    checks true, empty, prepare-error, overflow and unmodeled instances of its equivalence,
    and rejects random for every database and environment."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessQueries.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 4, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_column_groups_exclude_unique_key_conflicts(runtime_root: Path, tmp_path: Path) -> None:
    """GroupKeyConflictLaws proves the arbitrary-table implication and keeps its NULL
    asymmetry, ASCII-only NOCASE comparison and permutation of scan rows."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessGroupKeys.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") == 1, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_create_index_success_checks_schema_resolution_and_rows(runtime_root: Path, tmp_path: Path) -> None:
    """CreateIndexSuccess keeps exact free-database conditions, rejects preparation and
    restriction failures, checks unique rows, and admits partial indexes and repeated NULLs."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessCreateIndex.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") == 2, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_numeric_sum_bound_includes_real_and_null_cells(runtime_root: Path, tmp_path: Path) -> None:
    """SumBoundLaws supplies the free-input ledger bound for mixed numeric/NULL inputs,
    including REAL cells, SQL range checks and exact type metadata; source bridges permit sibling
    subqueries with explicit callbacks and nondefault prefixes. Kernel checks retain the first-prefix
    overflow boundary and exclude TEXT/BLOB values from the numeric range."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessSumBound.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") == 7, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_guide_email_success_uses_exact_corrected_precondition(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's uniqueEmail claim requires a physical table and a free index name, then
    derives its email column and uniqueness from Holds. Kernel cases include the complete
    precondition and retain the original name collision and ASCII-only NOCASE trap."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessUniqueEmail.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") == 1, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout


def test_guide_balance_success_derives_schema_and_numeric_bounds(runtime_root: Path, tmp_path: Path) -> None:
    """The physical-table premise and corrected SQL guard imply universal balance success,
    with written proofs for schema, metadata, storage affinity and SUM bounds. Kernel cases
    retain the missing-account and TEXT-overflow counterexamples and satisfy the full
    precondition on empty and mixed REAL/NULL tables. Compile the
    proof modules as a fresh consumer, then audit the final theorem's transitive axioms."""
    setup_path = module_setup(runtime_root, tmp_path)
    setup = json.loads(setup_path.read_text())
    for suffix in ("Syntax", "Resolution", "ResolveGuard", "Subqueries", "Observation", "Schema",
                   "Missing", "Success", ""):
        name = "SuccessBalance" + suffix
        setup["name"] = name
        setup_path.write_text(json.dumps(setup))
        artifact = tmp_path / f"{name}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup_path}",
                              "-o", str(artifact), str(FIXTURES / f"{name}.lean")],
                             cwd=tmp_path, timeout=60)
        assert result.returncode == 0, result.diagnostic()
        assert all(term not in result.stdout for term in ("sorryAx", "ofReduceBool", "_native")), result.stdout
        setup["importArts"][name] = [[str(artifact)]]
    assert result.stdout.count("depends on axioms") == 1, result.stdout
