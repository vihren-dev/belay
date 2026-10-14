"""The authored coverage cases of queries, numbers and writes (ADR 0012, slices 1 to 3c).

The cases of `conformance.authored_queries`, `conformance.authored_numbers`,
`conformance.authored_writes`, `conformance.authored_row_writes` and
`conformance.authored_deletes` are
recorded natively as version 5 records with statement outputs, name requirement
identifiers of the pinned documentation, and replay through resolution, the
execution semantics and query evaluation. Every case agrees with the model, and the
kernel checks each verdict, so the query and number semantics and their proofs run
on the same cases. The corpus writers publish each set as a new corpus, and the
boundary cases of `conformance.authored_obligations` as corpus 10.
"""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
from types import ModuleType

import pytest

from conformance import (authored_deletes, authored_numbers, authored_obligations, authored_queries,
                         authored_row_writes, authored_writes, delete_evidence, number_evidence, obligation_evidence,
                         query_evidence, row_write_evidence, write_evidence)
from conformance.model_check import compiled_many, prove
from conformance.native_replay import prepare
from conformance.record_parser import runtime_library
from conformance.requirement_coverage import resolved_ids

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
CASE_SETS = [authored_queries, authored_numbers, authored_writes, authored_row_writes, authored_deletes]
"""The authored case modules: each has `definitions` and `records`."""


@pytest.mark.parametrize("cases", CASE_SETS, ids=lambda module: module.__name__.rsplit(".", 1)[-1])
def test_coverage_cases_agree_with_kernel_proofs(cases: ModuleType, runtime_root: Path, tmp_path: Path) -> None:
    """Every case is a version 5 record with outputs and resolvable requirements, has a phase on
    each error, agrees in the compiled classifier, and has a kernel proof of its verdict."""
    recorded = cases.records()
    assert [record["name"] for record in recorded] == [case.name for case in cases.definitions()]
    resolved_ids(recorded, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    for record in recorded:
        assert record["nativeVersion"] == 5 and record["requirements"]
        assert all((event["phase"] is None) == (event["primaryCode"] == 0) for event in record["trace"])
    library = runtime_library(runtime_root)
    prepared = []
    for record in recorded:
        case, answer = prepare(record, library)
        assert case is not None and case["outputs"] is not None, (record["name"], answer)
        prepared.append(case)
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    assert {answer["verdict"] for answer in answers} == {"AGREE"}, answers
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
        list(pool.map(lambda index: prove(answers[index]["caseLean"], runtime_root, tmp_path / f"Case{index}.lean",
                                          case=prepared[index]), range(len(prepared))))


@pytest.mark.parametrize(("evidence", "cases", "version"), [(query_evidence, authored_queries, 7),
                                                            (number_evidence, authored_numbers, 8),
                                                            (write_evidence, authored_writes, 9),
                                                            (obligation_evidence, authored_obligations, 10),
                                                            (row_write_evidence, authored_row_writes, 11),
                                                            (delete_evidence, authored_deletes, 12)],
                         ids=["queries", "numbers", "writes", "obligations", "row-writes", "deletes"])
def test_coverage_corpus_round_trips(evidence: ModuleType, cases: ModuleType, version: int, tmp_path: Path) -> None:
    """The corpus writer writes a corpus of version 5 records that reads back unchanged and
    replays natively, and refuses to replace an existing directory."""
    from conformance.corpus import load
    manifest = evidence.publish(tmp_path / "corpus")
    assert manifest["nativeVersion"] == 5 and manifest["corpusVersion"] == version
    assert manifest["recordedCases"] == len(cases.definitions())
    assert load(tmp_path / "corpus")[0] == manifest
    with pytest.raises(ValueError, match="already exists"):
        evidence.publish(tmp_path / "corpus")
