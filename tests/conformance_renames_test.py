"""Native and kernel evidence for ALTER TABLE RENAME TO and RENAME COLUMN (ADR 0019, D4, part 2)."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from conformance import authored_renames
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
UNMODELED = {
    "rename-table-main-schema": "the translation refuses a schema-qualified table name in ALTER TABLE (form fullname)",
    "rename-column-view-recursive-aggregate": "SQLite accepts a recursive term with an aggregate in a stored view",
    "rename-column-check-loose-quote": "SQLite rewrites a double-quoted string of a CHECK text to single quotes",
    "rename-column-view-error": "a self-join with USING is outside the model, so the error is a restriction",
}
"""The cases the model does not describe, with the reason. Each one is a restriction of the model, never a
different answer: no case disagrees."""
PREDICT_TIMEOUT_SECONDS = 300
"""One predict run over all cases of the module."""


def test_rename_verdicts_of_the_judge(runtime_root: Path) -> None:
    """The subject's prediction of every case, judged as the judge does it, also for the cases with views
    and triggers: every case agrees with native SQLite except the ones that are restricted, and the failure
    of a dependent object, which SQLite reports while the statement runs, has the phase `step`."""
    records = authored_renames.records()
    assert [record["name"] for record in records] == [case.name for case in authored_renames.definitions()]
    assert set(UNMODELED) <= {record["name"] for record in records}
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    lines = "".join(json.dumps(subject_input(record), sort_keys=True) + "\n" for record in records)
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=lines, capture_output=True, text=True, timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    assert result.returncode == 0, result.stderr
    verdicts = {record["name"]: case_verdict(record, json.loads(line))
                for record, line in zip(records, result.stdout.splitlines(), strict=True)}
    assert len(verdicts) == len(records)
    assert {name for name, verdict in verdicts.items() if verdict.name == "MODEL_UNSUPPORTED"} == set(UNMODELED), verdicts
    assert {name for name, verdict in verdicts.items() if verdict.name not in ("AGREE", "MODEL_UNSUPPORTED")} == set(), verdicts
    phases = {record["name"]: [event.get("phase") for event in record["trace"]] for record in records}
    assert phases["rename-column-duplicate"] == ["step"]
    assert phases["rename-column-view-ambiguous"][0] == "step"
    assert phases["rename-table-taken"] == ["prepare"]


def test_rename_table_cases_in_the_kernel(runtime_root: Path, tmp_path: Path) -> None:
    """The cases whose database holds tables only (a view is judged through the predictions above) agree
    in the kernel: the model's catalog and rows after each statement are those of SQLite."""
    translator = runtime_translator(runtime_root)
    prepared = []
    for record in authored_renames.records():
        case, _ = prepare(record, translator)
        if case is not None and record["name"] not in UNMODELED:
            prepared.append(case)
    assert len(prepared) >= 25
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    assert all(answer["verdict"] == "AGREE" for answer in answers), [answer["verdict"] for answer in answers]
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared, name="Renames")
