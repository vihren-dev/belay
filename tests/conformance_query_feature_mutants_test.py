"""Each mutant of the subquery, expression form, DISTINCT and HAVING, foreign key, trigger,
possible result, parameter, compound and pragma mutant tables changes the verdict of an authored
case (ADR 0018 and ADR 0019).

These tests are the second half of the mutant tests of `tests/conformance_query_mutants_test.py`,
which describes the measurement and the time limit. They are in a separate file so that each file
stays short; they run in the same Nix suite, `mutants`.
"""

from pathlib import Path

import pytest

from conformance import (authored_compound, authored_distinct_having, authored_expression_forms,
                         authored_foreign_keys, authored_parameters, authored_possible_results, authored_pragmas,
                         authored_subqueries, authored_triggers, compound_mutants, distinct_having_mutants,
                         expression_form_mutants, foreign_key_mutants, parameter_mutants, possible_result_mutants,
                         pragma_mutants, subquery_mutants, trigger_mutants)
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]


def test_every_subquery_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored subquery cases notice every changed rule of subqueries
    (`conformance.subquery_mutants`): `NOT IN` that ignores a NULL, a correlated reference that
    does not read the outer row, a scalar subquery that gives its last row, and a name that
    resolves outward first (ADR 0018, slice 1)."""
    measure_set(runtime_root, [authored_subqueries], [(subquery_mutants.MUTANTS, subquery_mutants.TARGETS)])


def test_every_expression_form_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of the expression forms notice every changed rule
    (`conformance.expression_form_mutants`): an `IN` list under a right column's collation,
    `BETWEEN` that gives NULL before it checks for false, `CASE` whose NULL base matches a NULL
    `WHEN`, and `||` that skips a NULL operand (ADR 0018, slice 2)."""
    measure_set(runtime_root, [authored_expression_forms],
                [(expression_form_mutants.MUTANTS, expression_form_mutants.TARGETS)])


def test_every_distinct_having_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of DISTINCT, HAVING and aggregates inside expressions notice every
    changed rule (`conformance.distinct_having_mutants`): `HAVING` that keeps a NULL group, an
    aggregate over the first row of its group only, and `DISTINCT` that keeps every NULL row
    (ADR 0018, slice 3)."""
    measure_set(runtime_root, [authored_distinct_having],
                [(distinct_having_mutants.MUTANTS, distinct_having_mutants.TARGETS)])


def test_every_foreign_key_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of enforced foreign keys (ADR 0018, slice 4) notice every changed
    rule (`conformance.foreign_key_mutants`): a check of a composite child key with one NULL
    column, `SET NULL` that deletes the child row, `CASCADE` on update that keeps the old child
    key, and a lookup that compares the child value without the parent key's affinity."""
    measure_set(runtime_root, [authored_foreign_keys], [(foreign_key_mutants.MUTANTS, foreign_key_mutants.TARGETS)])


def test_every_trigger_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of triggers (ADR 0018, slice 5) notice every changed rule
    (`conformance.trigger_mutants`): triggers that run oldest first, `WHEN` that a NULL passes,
    `RAISE(IGNORE)` in an `AFTER` trigger that still runs the later triggers of the row, `UPDATE OF`
    that runs for every `UPDATE`, and a trigger that fires itself."""
    measure_set(runtime_root, [authored_triggers], [(trigger_mutants.MUTANTS, trigger_mutants.TARGETS)])


def test_every_possible_result_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of the results that SQLite may give (ADR 0018, slice 6) notice every
    changed rule (`conformance.possible_result_mutants`): a list that ignores `OFFSET`, a list with
    only the choice of `Query.results`, a list that cuts a group with one row too many, and groups
    that `DESC` does not reverse."""
    measure_set(runtime_root, [authored_possible_results],
                [(possible_result_mutants.MUTANTS, possible_result_mutants.TARGETS)])


def test_every_parameter_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of parameters (ADR 0019, slice 1) notice every changed rule of the model
    (`conformance.parameter_mutants`): a parameter with an affinity, `ORDER BY ?` as a column
    number, and a `LIMIT ?` that accepts a real with a fraction."""
    measure_set(runtime_root, [authored_parameters], [(parameter_mutants.MUTANTS, parameter_mutants.TARGETS)])


def test_every_compound_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of compound SELECT (ADR 0019, slice 3) notice every changed rule of the
    model (`conformance.compound_mutants`): operators that group from the right, `EXCEPT` with
    duplicates, NULL unequal to NULL, the compound collation from the right-most term or always
    `BINARY`, `IN` with the compound collation, the right term of `EXCEPT` run after empty left
    rows, and an `ORDER BY` term sorted under `BINARY`."""
    measure_set(runtime_root, [authored_compound], [(compound_mutants.MUTANTS, compound_mutants.TARGETS)])


def test_every_pragma_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored cases of pragmas (ADR 0019, slice 2) notice every changed rule of the model
    (`conformance.pragma_mutants`): `fkid` in declaration order, `foreign_key_check` that skips a
    missing parent table, `table_info` with the `cid` of every column, and REPLACE deletes that
    fire no trigger with recursive triggers on."""
    measure_set(runtime_root, [authored_pragmas], [(pragma_mutants.MUTANTS, pragma_mutants.TARGETS)])
