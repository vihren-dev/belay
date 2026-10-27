"""Native and kernel evidence for INSERT from a query (ADR 0019, D4, amended 2026-10-25)."""

import json
from pathlib import Path

import pytest

from conformance import authored_insert_queries
from conformance.model_assertions import FOOTER, HEADER, case_assertions
from conformance.model_check import compiled_many, kernel_check, prove_all
from conformance.native_replay import prepare
from conformance.requirement_coverage import resolved_ids
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The repository root, from which the test reads conformance/requirements-3.51.0.json."""
UNMODELED = {"insert-query-group-by", "insert-query-compound", "insert-query-sorted-without-index",
             "insert-query-sorted-with-index", "insert-query-transfer-with-rowid-gap",
             "insert-query-transfer-column-list", "insert-query-trigger-two-orders"}
"""The cases whose source the model does not describe: grouping and compounds give rows in an order
that the model does not know, an ORDER BY over a source that may fail has no known failing row, and
SQLite's transfer optimization copies rows under the rowids of the source. A trigger with a source
that SQLite may read in two orders has no description either: its log depends on the order."""
ORDER_CASES = {"insert-query-index-order", "insert-query-index-order-keeps-other-rows"}
"""The cases whose native rows follow the index of the source, not its scan: the model agrees only
through its second execution."""


def test_insert_query_native_and_kernel_verdicts(runtime_root: Path, tmp_path: Path) -> None:
    """INSERT from a query agrees with native SQLite in every case that the model describes, also
    where SQLite read the source by an index (the model's second execution); the cases it does not
    describe stay unmodeled. The kernel checks both verdict classes over the runner's decoded cases
    and their original JSON."""
    records = authored_insert_queries.records()
    assert [record["name"] for record in records] == [case.name for case in authored_insert_queries.definitions()]
    assert ORDER_CASES | UNMODELED <= {record["name"] for record in records}
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    translator = runtime_translator(runtime_root)
    prepared = []
    for record in records:
        case, answer = prepare(record, translator)
        assert case is not None and case["outputs"] is not None and case["continues"], (record["name"], answer)
        prepared.append(case)
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    agreeing_cases, agreeing_terms, boundaries = [], [], []
    for index, (record, case, answer) in enumerate(zip(records, prepared, answers, strict=True)):
        unmodeled = record["name"] in UNMODELED
        assert answer["verdict"] == ("MODEL_UNSUPPORTED" if unmodeled else "AGREE"), (record["name"], answer)
        if unmodeled:
            boundaries.append(f"namespace Boundary{index}\n" +
                case_assertions(answer["caseLean"], json.dumps(case, ensure_ascii=False), expected=False) +
                "theorem sourceUnsupported : classifyCase fixture = .modelUnsupported := by decide +kernel\n"
                f"#print axioms sourceUnsupported\nend Boundary{index}\n")
        else:
            agreeing_cases.append(case)
            agreeing_terms.append(answer["caseLean"])
    assert len(boundaries) == len(UNMODELED)
    prove_all(agreeing_terms, runtime_root, tmp_path, cases=agreeing_cases, name="InsertQueries")
    destination = tmp_path / "InsertQueryBoundaries.lean"
    destination.write_text(HEADER + "".join(boundaries) + FOOTER)
    output = kernel_check(runtime_root, destination)
    assert output.count("sourceUnsupported' depends on axioms") == len(UNMODELED)
