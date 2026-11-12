"""Claims over every database (ADR 0017, S4; `Belay/Sqlite/{Programs/Scripts,Tooling/Counterexamples}/QueryBridge.lean`,
`Belay/Sqlite/Queries/Evaluation/SqlSimpLaws.lean` and the model's laws of the expressions of a condition). Each fixture proves its claims for an arbitrary database and checks
each claim on a concrete database, so that no lemma is vacuous. The fixture fails to elaborate
when a proof or an instance does not hold.
"""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import COUNT_SUPPORT, DUPLICATE_KEY_SUPPORT, check_module_chain
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_view_catalog_keeps_unresolved_definitions_and_refuses_unexpanded_uses(runtime_root: Path, tmp_path: Path) -> None:
    """The view catalog stores written queries, owns no rows, distinguishes FK mismatch,
    a write or schema change of a view is a prepare error, and a table-valued metadata function of
    a view is refused instead of fabricating an empty result."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsViewCatalog.lean"), tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_expression_laws_turn_a_condition_into_logic(runtime_root: Path, tmp_path: Path) -> None:
    """The simp set `sql_simp` resolves a written condition (`BETWEEN`, `AND`, `NOT`, `OR`, `IS NULL`,
    a parameter) to the resolved expression with the affinity and collation of its columns, shows
    that the expression is calm, and turns the truth of `AND`, `OR` and `IS NULL` into Booleans."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsExpressionLaws.lean"), tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_no_row_or_some_row_satisfies_a_condition_in_a_subquery(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE [NOT] EXISTS (SELECT 1 FROM t WHERE p)` over every database: the claims are proved
    through the phase rules (`Run.query_returnsResult_faultless`, the subquery run rule) with the support of
    `SelectOneWhereSupport`, with instances on databases where `decide +kernel` checks both sides. The
    axiom audit shows that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (("SelectOneWhereSupport", 3), ("ClaimsExists", 3)), timeout=90)


def test_a_where_that_may_fail_has_no_modeled_output(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 FROM t WHERE abs(x) = 1` (and the same call in a subquery of `EXISTS`) on a table with the
    smallest 64-bit integer and the integer 1: SQLite can fail at the call of `abs` on the smallest integer, so
    the model does not describe the statement. None of `Holds`, `Empty` and `Fails` holds, by `decide +kernel`
    and by the rule of a SELECT that is not ready (`Run.send_unready`) over every database. The axiom audit
    shows that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (("ClaimsMayFail", 2),), timeout=90)


def test_the_number_of_rows_of_a_table_is_compared_with_a_parameter(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE (SELECT count(*) FROM t [WHERE p]) = $n` over every database: `Holds` means that the
    table has `n` rows (or `n` rows for which `p` is true), proved through the phase rules with the support of
    `SelectCountWhereSupport`, with instances on one database where `decide +kernel` checks the claim for a true
    and for a false `n`. The axiom audit shows that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (*COUNT_SUPPORT, ("ClaimsCount", 3)), timeout=90)


def test_a_parameter_is_in_a_column_of_a_table(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE $x IN (SELECT e FROM t [WHERE p])` over every database: `Holds` means that some stored
    row has a value of `e` that equals `x` under the comparison of `IN`, proved through the phase rules with the
    support of `SelectColumnWhereSupport`, with instances on one database where `decide +kernel` checks the claim
    for a true and for a false `x`. The axiom audit shows that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (("SelectOneWhereSupport", 3), ("SelectColumnWhereSupport", 2),
                                                ("ClaimsIn", 2)), timeout=90)


def test_a_table_has_a_column_according_to_pragma_table_info(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 FROM pragma_table_info('t') WHERE name = 'c'` over every database: `Holds` means that the table
    has a column that is not generated with the name `c` as bytes, so the table lookup ignores ASCII case and the
    name test does not, proved with the pragma source rule of a SELECT and `sql_simp`, with instances on one
    database where `decide +kernel` checks the claim for a true and for a false name."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsTableInfo.lean"), tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_no_two_rows_of_a_table_have_equal_keys(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t GROUP BY k HAVING count(*) > 1)` over every database: `Holds`
    means that no group of rows with equal keys has more than one row, proved through the phase rules with the
    support of `SelectDuplicateKeySupport`, with instances on three databases where `decide +kernel` checks the
    claim: different keys, keys that differ only in case under `NOCASE`, and two NULL keys. The axiom audit shows
    that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (("SelectOneWhereSupport", 3), *DUPLICATE_KEY_SUPPORT,
                                                ("ClaimsDuplicateKeys", 5)), timeout=90)


def test_a_unique_lookup_matches_at_most_one_row(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE (SELECT count(*) FROM t WHERE c = $v) <= 1` over every database whose table has `c` under a
    `UNIQUE` constraint or as its `PRIMARY KEY`: the claim holds, proved through the phase rules with the support of
    `SelectCountWhereSupport` and the unique keys of the valid database, with instances on databases where
    `decide +kernel` checks it: a stored and an unknown address, the affinity of an `INTEGER` column, and a `NOCASE`
    column with a `BINARY` unique index, where the bound fails because the collations differ. The axiom audit shows
    that no proof is missing."""
    check_module_chain(runtime_root, tmp_path, (*COUNT_SUPPORT, ("ClaimsUniqueLookup", 1)), timeout=90)


def test_derived_sources_reach_public_query_predicates(runtime_root: Path, tmp_path: Path) -> None:
    """SQL quotations resolve derived tables into the existing query evaluator: metadata,
    compound columns, enclosing scope, empty sources, prepare errors and uncertain membership.
    Named-table and pragma laws also accept arbitrary source callbacks and nested prefixes."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsDerived.lean"), tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_common_tables_reach_public_queries_and_writes(runtime_root: Path, tmp_path: Path) -> None:
    """CommonTableExpansion preserves names, scope, errors and the values of CTE-backed writes
    through sql/db! quotations and kernel-checked public query predicates."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsCommonTables.lean"), tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_expression_congruence_preserves_observations(runtime_root: Path, tmp_path: Path) -> None:
    """ExprCongruence and its context/append laws keep faults, subtype and distinct
    certainty observations under their independent locality and row-width premises."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsExpressionCongruence.lean"), tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 3, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
