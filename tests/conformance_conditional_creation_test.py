"""Native and kernel evidence for CREATE TABLE and CREATE INDEX with IF NOT EXISTS (ADR 0030, slice 1)."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from conformance import authored_conditional_creation
from conformance.model_check import compiled_many, prove_all
from conformance.native_replay import prepare
from conformance.requirement_coverage import resolved_ids
from conformance.sql_text import runtime_translator
from judge.compare import case_verdict
from judge.records import subject_input

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The repository root, from which the test reads conformance/requirements-3.51.0.json."""
PREDICT_TIMEOUT_SECONDS = 300
"""One predict run over all cases of the module."""


def test_conditional_creation_verdicts_of_the_judge(runtime_root: Path) -> None:
    """The subject's prediction of every case (`{Queries/Preparation,Schema/Ddl}/ConditionalCreation.lean` and the translation of the
    clause), judged as the judge does it: every case agrees with native SQLite, and the no-op cases stop SQLite
    before it reads the rest of the statement."""
    records = authored_conditional_creation.records()
    assert [record["name"] for record in records] == [case.name for case in authored_conditional_creation.definitions()]
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    lines = "".join(json.dumps(subject_input(record), sort_keys=True) + "\n" for record in records)
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=lines, capture_output=True, text=True, timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    assert result.returncode == 0, result.stderr
    verdicts = {record["name"]: case_verdict(record, json.loads(line))
                for record, line in zip(records, result.stdout.splitlines(), strict=True)}
    assert len(verdicts) == len(records)
    assert {name: verdict.name for name, verdict in verdicts.items() if verdict.name != "AGREE"} == {}, verdicts


def test_conditional_creation_cases_in_the_kernel(runtime_root: Path, tmp_path: Path) -> None:
    """The cases whose database holds tables and indexes only agree in the kernel: the model's catalog and rows
    after each statement are those of SQLite."""
    translator = runtime_translator(runtime_root)
    prepared = []
    for record in authored_conditional_creation.records():
        case, _ = prepare(record, translator)
        if case is not None:
            prepared.append(case)
    assert len(prepared) >= 10
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    assert all(answer["verdict"] == "AGREE" for answer in answers), [answer["verdict"] for answer in answers]
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared,
              name="ConditionalCreation")
