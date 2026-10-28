"""Native and kernel evidence for the table rebuild of the guide (ADR 0019, D4, part 3)."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from conformance import authored_rebuilds
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
    "rebuild-drop-column-instead": "the table is the parent of a foreign key, so the drop is a restriction of the model",
    "rebuild-view-blocks-rename": "a record with a view is judged through its predictions, not through the kernel",
}
"""The cases the kernel does not prove, with the reason. Each one is a restriction of the model or a case with a
view, never a different answer: the judge's verdict of every case but the restricted one is AGREE."""
RESTRICTED = {"rebuild-drop-column-instead"}
"""The cases that the model restricts."""
PREDICT_TIMEOUT_SECONDS = 300
"""One predict run over all cases of the module."""


def test_rebuild_verdicts_of_the_judge(runtime_root: Path) -> None:
    """The subject's prediction of every rebuild case, judged as the judge does it: the unsafe rebuild cascades,
    the corrected rebuild keeps the rows and finds the expected violations, the pragma in a transaction changes
    nothing, a rename of the old table moves the foreign keys of its children, a view blocks the rename, and a rollback
    restores the tables. Every case agrees with native SQLite except the one that is restricted."""
    records = authored_rebuilds.records()
    assert [record["name"] for record in records] == [case.name for case in authored_rebuilds.definitions()]
    assert set(UNMODELED) <= {record["name"] for record in records}
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    lines = "".join(json.dumps(subject_input(record), sort_keys=True) + "\n" for record in records)
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=lines, capture_output=True, text=True, timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    assert result.returncode == 0, result.stderr
    verdicts = {record["name"]: case_verdict(record, json.loads(line))
                for record, line in zip(records, result.stdout.splitlines(), strict=True)}
    assert {name for name, verdict in verdicts.items() if verdict.name == "MODEL_UNSUPPORTED"} == RESTRICTED, verdicts
    assert {name for name, verdict in verdicts.items() if verdict.name not in ("AGREE", "MODEL_UNSUPPORTED")} == set(), verdicts


def test_rebuild_cases_in_the_kernel(runtime_root: Path, tmp_path: Path) -> None:
    """The cases whose database holds tables only agree in the kernel and are proved there: the model's catalog and
    rows after each statement of the rebuild are those of SQLite, with enforcement on and off."""
    translator = runtime_translator(runtime_root)
    prepared = []
    for record in authored_rebuilds.records():
        case, _ = prepare(record, translator)
        if case is not None and record["name"] not in UNMODELED:
            prepared.append(case)
    assert len(prepared) >= 8
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    assert all(answer["verdict"] == "AGREE" for answer in answers), [answer["verdict"] for answer in answers]
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared, name="Rebuilds")
