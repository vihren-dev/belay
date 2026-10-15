"""Each mutant of the query, number, key, write, row-write, DELETE, join and alias mutant tables
changes the verdict of an authored case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and its slices add the number, write, join and key rules: a changed copy of
the model that no case notices shows a missing case. The cases are the authored cases of
`conformance.authored_queries`, `authored_numbers`, `authored_keys`, `authored_writes`,
`authored_row_writes`, `authored_deletes`, `authored_joins`, `authored_using`,
`authored_right`, `authored_merged` and `authored_aliases`, recorded natively with their outputs. Two
measurements, one for queries, numbers and keys and one for writes, joins and aliases, each build
one base copy for their mutants, which keeps each test within its time limit on a hosted
runner; every case must agree with the base copy. Each mutant copy then classifies the
case that the mutant names as its target, which keeps the elaboration of case terms
short.
"""

from pathlib import Path

import pytest

from conformance import (alias_mutants, authored_aliases, authored_deletes, authored_joins, authored_keys,
                         authored_merged, authored_numbers, authored_queries, authored_right, authored_row_writes,
                         authored_using, authored_writes)
from conformance.native_replay import prepare
from conformance import (delete_mutants, join_mutants, key_mutants, merged_mutants, number_mutants, query_mutants,
                         right_mutants, row_write_mutants, using_mutants, write_mutants)
from conformance.case_format import Json
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


Mutants = dict[str, tuple[str, str, str]]
"""A mutant table: the file, the exact text and the replacement of each mutant."""
Targets = dict[str, tuple[str, ...]]
"""The target cases of each mutant."""


def measure_set(runtime_root: Path, records: list[dict[str, Json]], tables: list[tuple[Mutants, Targets]]) -> None:
    """Every case of the records agrees with the unchanged model, and every mutant of the mutant
    tables changes the verdict of its target case."""
    library = runtime_library(runtime_root)
    cases = []
    for record in records:
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    mutants: Mutants = {}
    targets: Targets = {}
    for table, table_targets in tables:
        assert not set(table) & set(mutants), "mutant names must be unique"
        mutants |= table
        targets |= table_targets
    result = measure(cases, ROOT, runtime_root, mutants, targets)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"


def test_every_query_and_number_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored query, number and key cases notice every changed rule of query semantics,
    numbers and unique key values (`conformance.query_mutants`, `conformance.number_mutants`,
    `conformance.key_mutants`), so these rules are tested."""
    measure_set(runtime_root, authored_queries.records() + authored_numbers.records() + authored_keys.records(),
                [(query_mutants.MUTANTS, query_mutants.TARGETS), (number_mutants.MUTANTS, number_mutants.TARGETS),
                 (key_mutants.MUTANTS, key_mutants.TARGETS)])


def test_every_write_and_join_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The authored write and join cases notice every changed rule of writes with output, of
    row-dependent writes, of DELETE and of joins (`conformance.write_mutants`,
    `conformance.row_write_mutants`, `conformance.delete_mutants`, `conformance.join_mutants`,
    `conformance.using_mutants`, `conformance.right_mutants`, `conformance.merged_mutants`,
    `conformance.alias_mutants`), so these rules are tested. The joins
    share this measurement, which is the shorter one, to keep each test within its time
    limit."""
    measure_set(runtime_root, authored_writes.records() + authored_row_writes.records() + authored_deletes.records()
                + authored_joins.records() + authored_using.records() + authored_right.records()
                + authored_merged.records() + authored_aliases.records(),
                [(write_mutants.MUTANTS, write_mutants.TARGETS), (row_write_mutants.MUTANTS, row_write_mutants.TARGETS),
                 (delete_mutants.MUTANTS, delete_mutants.TARGETS), (join_mutants.MUTANTS, join_mutants.TARGETS),
                 (using_mutants.MUTANTS, using_mutants.TARGETS), (right_mutants.MUTANTS, right_mutants.TARGETS),
                 (merged_mutants.MUTANTS, merged_mutants.TARGETS), (alias_mutants.MUTANTS, alias_mutants.TARGETS)])
