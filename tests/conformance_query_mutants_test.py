"""Each mutant of the query, number, key, alias, UPSERT, algorithm, query-without-FROM, JSON,
JSON function, `json_each`, clock, date function and date modifier mutant tables changes the verdict
of an authored case. The mutants of subqueries, expression forms, DISTINCT and HAVING, foreign keys,
triggers, possible results, parameters, compound SELECT and pragmas are in
`tests/conformance_query_feature_mutants_test.py`, so that each file stays short.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and its slices add the number, write, join and key rules: a changed copy of the
model that no case notices shows a missing case. The cases are the authored cases of the
`conformance.authored_*` module of each table, recorded natively with their outputs. The mutants
of writes, joins and table forms are in `tests/conformance_table_mutants_test.py`, a separate Nix
suite, so that each suite stays within its time limit on a hosted runner. Each test is one
measurement, which builds one base copy for its mutants (`measure_set`) and then the mutant
copies in parallel. Each of the three Nix suites of mutants has its own job on its own hosted
runner (`.github/workflows/ci.yml`). A hosted runner is slower than this development machine: a
measurement that took 160.6 seconds here took more than the limit of 300 seconds there, so the
local target for a measurement is about 125 seconds. The base copy and most mutant copies build
almost every module, so the time of a measurement grows with the number of mutant copies that
build many modules.

Three groups of mutants were each one measurement that was too slow, and are now split:

- The number and query-without-FROM mutants (17) took 176 seconds alone on eight cores (October
  2026). As three measurements, of the 6 mutants of arithmetic, the other 7 number mutants and
  the 4 mutants of queries without FROM, each took at most 124 seconds alone.
- The 16 query mutants took 160.6 seconds in a focused local run, and more than 300 seconds on a
  hosted runner. As three measurements by model file, of the 3 mutants of `Comparison.lean`, the
  7 mutants of `QueryEval.lean` and `QueryResults.lean`, and the 6 mutants of the `Resolution`
  folder, they took 109.5, 82.9 and 72.5 seconds.
- The 14 JSON mutants took 194.1 seconds in a focused local run. As two measurements, of the 8
  mutants of JSON reading and the 6 mutants of the JSON functions, they took 122.8 and 112.5
  seconds.

The measurements of the query and JSON splits ran while another Nix build used the same eight
cores (load average about 14), so each is an upper bound of its time alone. The hosted run is
the validation of the limits.

Every case must agree with the base copy. Each mutant copy then classifies the case that the
mutant names as its target, which keeps the elaboration of case terms short.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from conformance import (algorithm_mutants, alias_mutants, authored_algorithms, authored_aliases, authored_clock,
                         authored_date_functions, authored_date_modifiers, authored_fromless, authored_json,
                         authored_json_each, authored_json_functions, authored_keys, authored_numbers,
                         authored_queries, authored_upserts, clock_mutants, date_function_mutants,
                         date_modifier_mutants, fromless_mutants, json_each_mutants, json_function_mutants,
                         json_mutants, upsert_mutants)
from conformance import key_mutants, number_mutants, query_mutants
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


def number_mutant_table(arithmetic: bool) -> tuple[Mutants, Targets]:
    """The number mutants of `conformance.number_mutants` in `Arithmetic.lean`, or the others,
    with their targets: two measurements, each within the time limit."""
    mutants = {name: mutant for name, mutant in number_mutants.MUTANTS.items()
               if (mutant[0] == number_mutants.ARITHMETIC) == arithmetic}
    return mutants, {name: number_mutants.TARGETS[name] for name in mutants}


def test_every_arithmetic_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored number cases notice every changed rule of arithmetic and `CAST` to INTEGER
    (the mutants of `conformance.number_mutants` in `Arithmetic.lean`)."""
    measure_set(runtime_root, [authored_numbers], [number_mutant_table(True)])


def test_every_other_number_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored number cases notice every changed rule of sums and averages, number text,
    and `coalesce` (the other mutants of `conformance.number_mutants`)."""
    measure_set(runtime_root, [authored_numbers], [number_mutant_table(False)])


def test_every_fromless_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query-without-FROM cases notice every changed rule of queries without FROM
    (`conformance.fromless_mutants`)."""
    measure_set(runtime_root, [authored_fromless], [(fromless_mutants.MUTANTS, fromless_mutants.TARGETS)])


def test_every_json_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored JSON cases notice every changed rule of JSON reading and `json_extract`
    (`conformance.json_mutants`)."""
    measure_set(runtime_root, [authored_json], [(json_mutants.MUTANTS, json_mutants.TARGETS)])


def test_every_json_function_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored JSON function cases notice every changed rule of `json_type`, `json_valid`,
    `json_array_length` and `json` (`conformance.json_function_mutants`)."""
    measure_set(runtime_root, [authored_json_functions],
                [(json_function_mutants.MUTANTS, json_function_mutants.TARGETS)])


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
