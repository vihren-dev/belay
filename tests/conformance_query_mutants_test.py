"""Each mutant of the query, number, key, alias, UPSERT, algorithm, query-without-FROM, JSON,
JSON function, `json_each`, clock, date function and date modifier mutant tables changes the
verdict of an authored case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and its slices add the number, write, join and key rules: a changed copy of the
model that no case notices shows a missing case. The cases are the authored cases of
`conformance.authored_queries`, `authored_numbers`, `authored_keys`, `authored_aliases`,
`authored_upserts`, `authored_algorithms`, `authored_fromless`, `authored_json`,
`authored_json_functions`, `authored_json_each`, `authored_clock`, `authored_date_functions`
and `authored_date_modifiers`, recorded natively with their outputs. The mutants of writes,
joins and table forms are in `tests/conformance_table_mutants_test.py`, a separate Nix suite,
so that each suite stays within its time limit on a hosted runner. Seven measurements of at
most 17 mutants each, one for queries, one for numbers and queries without FROM, one for the
JSON functions, one for `json_each` and the clock, one for the date and time functions and
their modifiers, one for keys and rowid aliases, and one for UPSERT and conflict algorithms,
each build one base copy for their mutants (`measure_set`). The two Nix suites of mutants run at
the same time on a hosted runner, which slows each test about twice, so each test stays far
within its limit of 300 seconds; every case must agree with the base copy. Each mutant copy
then classifies the case that the mutant names as its target, which keeps the elaboration of
case terms short.
"""

from pathlib import Path

import pytest

from conformance import (algorithm_mutants, alias_mutants, authored_algorithms, authored_aliases, authored_clock,
                         authored_date_functions, authored_date_modifiers, authored_fromless, authored_json,
                         authored_json_each, authored_json_functions, authored_keys, authored_numbers,
                         authored_queries, authored_upserts, clock_mutants, date_function_mutants,
                         date_modifier_mutants, fromless_mutants, json_each_mutants, json_function_mutants,
                         json_mutants, upsert_mutants)
from conformance import key_mutants, number_mutants, query_mutants
from tests.mutant_sets import measure_set

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]

def test_every_query_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query cases notice every changed rule of query semantics
    (`conformance.query_mutants`), so these rules are tested."""
    measure_set(runtime_root, [authored_queries], [(query_mutants.MUTANTS, query_mutants.TARGETS)])


def test_every_number_and_fromless_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored number and query-without-FROM cases notice every changed rule of numbers
    and of queries without FROM (`conformance.number_mutants`, `conformance.fromless_mutants`)."""
    measure_set(runtime_root, [authored_numbers, authored_fromless],
                [(number_mutants.MUTANTS, number_mutants.TARGETS),
                 (fromless_mutants.MUTANTS, fromless_mutants.TARGETS)])


def test_every_json_function_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored JSON and JSON function cases notice every changed rule of the JSON functions
    (`conformance.json_mutants`, `conformance.json_function_mutants`)."""
    measure_set(runtime_root, [authored_json, authored_json_functions],
                [(json_mutants.MUTANTS, json_mutants.TARGETS),
                 (json_function_mutants.MUTANTS, json_function_mutants.TARGETS)])


def test_every_json_each_and_clock_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored `json_each` and clock cases notice every changed rule of `json_each` and the
    clock (`conformance.json_each_mutants`, `conformance.clock_mutants`)."""
    measure_set(runtime_root, [authored_json_each, authored_clock],
                [(json_each_mutants.MUTANTS, json_each_mutants.TARGETS),
                 (clock_mutants.MUTANTS, clock_mutants.TARGETS)])


def test_every_date_function_and_modifier_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored date and time function and modifier cases notice every changed rule of
    the date and time functions and their modifiers (`conformance.date_function_mutants`,
    `conformance.date_modifier_mutants`), so these rules are tested."""
    measure_set(runtime_root, [authored_date_functions, authored_date_modifiers],
                [(date_function_mutants.MUTANTS, date_function_mutants.TARGETS),
                 (date_modifier_mutants.MUTANTS, date_modifier_mutants.TARGETS)])


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
