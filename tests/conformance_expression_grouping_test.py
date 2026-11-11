"""Native evidence for grouping terms that are expressions (ADR 0030, slice 3)."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from conformance import authored_expression_grouping
from conformance.requirement_coverage import resolved_ids
from judge.compare import case_verdict
from judge.records import subject_input

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The repository root, from which the test reads conformance/requirements-3.51.0.json."""
PREDICT_TIMEOUT_SECONDS = 300
"""One predict run over all cases of the module."""


def test_expression_grouping_verdicts_of_the_judge(runtime_root: Path) -> None:
    """The subject's prediction of every case (`resolveGroupTermTraced` and `resolveGroupExpressionTraced` of
    `Queries/Select/QueryAggregates.lean`, and the association of `Queries/Select/GroupAssociation.lean`), judged as the
    judge does it: every case agrees with native SQLite, so expression terms group, collate, number and give the
    values of a group as SQLite does."""
    records = authored_expression_grouping.records()
    assert [record["name"] for record in records] == [case.name for case in
                                                     authored_expression_grouping.definitions()
                                                     + authored_expression_grouping.date_cases()]
    resolved_ids(records, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    lines = "".join(json.dumps(subject_input(record), sort_keys=True) + "\n" for record in records)
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=lines, capture_output=True, text=True, timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    assert result.returncode == 0, result.stderr
    verdicts = {record["name"]: case_verdict(record, json.loads(line))
                for record, line in zip(records, result.stdout.splitlines(), strict=True)}
    assert len(verdicts) == len(records)
    assert {name: verdict.name for name, verdict in verdicts.items() if verdict.name != "AGREE"} == {}, verdicts
