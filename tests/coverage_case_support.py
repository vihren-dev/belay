"""The check that the authored coverage test files share.

The coverage cases are in two test files, so that two Nix suites (`coverageStatements` and
`coverageFeatures` in `build-support/tests.nix`) share their kernel proofs: one suite took
more than 1160 s on hosted macOS when it held them all. Each test file lists its case modules
and calls `check_coverage_cases` for each of them.
"""

import json
from pathlib import Path
from types import ModuleType

from conformance import authored_after_error, authored_counters, authored_foreign_key_atoms
from conformance.model_check import compiled_many, prove_all
from conformance.native_replay import prepare
from conformance.requirement_coverage import resolved_ids
from conformance.sql_text import runtime_translator

ROOT = Path(__file__).resolve().parents[1]


def native_record_version(cases: ModuleType) -> int:
    """The native record version of a case module: 7 for the connection counters (ADR 0024),
    6 for the cases that run on after an error, else 5 (statement outputs)."""
    return 7 if cases is authored_counters else 6 if cases in (authored_after_error, authored_foreign_key_atoms) else 5


def check_coverage_cases(cases: ModuleType, runtime_root: Path, tmp_path: Path) -> None:
    """Check that every case of a module is a native record with outputs, has resolvable
    requirements, has a phase on each error, agrees in the compiled classifier, and has a
    kernel proof of its verdict (`conformance.model_check.prove_all`)."""
    records = cases.records()
    assert [record["name"] for record in records] == [case.name for case in cases.definitions()]
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    for record in records:
        assert record["nativeVersion"] == native_record_version(cases) and record["requirements"]
        assert all((event["phase"] is None) == (event["primaryCode"] == 0) for event in record["trace"])
    translator = runtime_translator(runtime_root)
    prepared = []
    for record in records:
        case, answer = prepare(record, translator)
        assert case is not None and case["outputs"] is not None, (record["name"], answer)
        prepared.append(case)
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    assert {answer["verdict"] for answer in answers} == {"AGREE"}, answers
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared)
