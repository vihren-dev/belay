"""The authored coverage cases of single-table queries (`conformance.authored_queries`, ADR 0012).

Each case is recorded natively as a version 5 record with statement outputs, names
requirement identifiers of the pinned documentation, and replays through
resolution, the execution semantics and query evaluation. Every case agrees with
the model, and the kernel checks each verdict, so the query semantics and their
proofs run on the same cases.
"""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path

import pytest

from conformance.authored_queries import definitions, records
from conformance.model_check import compiled_many, prove
from conformance.native_replay import prepare
from conformance.record_parser import runtime_library
from conformance.requirement_coverage import resolved_ids

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_coverage_cases_agree_with_kernel_proofs(runtime_root: Path, tmp_path: Path) -> None:
    """Every case is a version 5 record with outputs and resolvable requirements, has a phase on
    each error, agrees in the compiled classifier, and has a kernel proof of its verdict."""
    recorded = records()
    assert [record["name"] for record in recorded] == [case.name for case in definitions()]
    resolved_ids(recorded, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    for record in recorded:
        assert record["nativeVersion"] == 5 and record["requirements"]
        assert all((event["phase"] is None) == (event["primaryCode"] == 0) for event in record["trace"])
    library = runtime_library(runtime_root)
    cases = []
    for record in recorded:
        case, answer = prepare(record, library)
        assert case is not None and case["outputs"] is not None, (record["name"], answer)
        cases.append(case)
    answers = compiled_many(cases, runtime_root, emit_lean=True)
    assert {answer["verdict"] for answer in answers} == {"AGREE"}, answers
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
        list(pool.map(lambda index: prove(answers[index]["caseLean"], runtime_root, tmp_path / f"Query{index}.lean",
                                          case=cases[index]), range(len(cases))))


def test_coverage_corpus_round_trips(tmp_path: Path) -> None:
    """`conformance.query_evidence.publish` writes a corpus of version 5 records that reads back
    unchanged and replays natively, and refuses to replace an existing directory."""
    from conformance.corpus import load
    from conformance.query_evidence import publish
    manifest = publish(tmp_path / "corpus")
    assert manifest["nativeVersion"] == 5 and manifest["corpusVersion"] == 7
    assert manifest["recordedCases"] == len(definitions())
    assert load(tmp_path / "corpus")[0] == manifest
    with pytest.raises(ValueError, match="already exists"):
        publish(tmp_path / "corpus")
