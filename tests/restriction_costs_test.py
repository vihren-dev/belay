"""`conformance.restriction_costs` counts the cases out of scope by their cause.

The report ranks which model restriction to lift next, from the subject's predictions
of the claimed corpora. This test checks the counting on a small fixed set of
predictions: restriction ids, frontend refusals by the first clause of their message,
undeclared cases, and cases in scope, which count nowhere.
"""

import json
from pathlib import Path

import pytest

from conformance.restriction_costs import costs

pytestmark = [pytest.mark.unit]


def test_costs_count_each_cause(tmp_path: Path) -> None:
    """Each prediction counts once, under its cause, and the corpus sizes are kept."""
    lines = [
        {"name": "a", "status": "unsupported", "reason": "REAL values are not modeled; use an integer",
         "restriction": "real-value"},
        {"name": "b", "status": "unsupported", "reason": "REAL values are not modeled; use an integer",
         "restriction": "real-value"},
        {"name": "c", "status": "unsupported", "reason": "This statement is not modeled; the model runs ..."},
        {"name": "d", "status": "predicted", "supported": False, "steps": []},
        {"name": "e", "status": "predicted", "supported": True, "steps": []},
    ]
    (tmp_path / "corpus-v1.jsonl").write_text("".join(json.dumps(line) + "\n" for line in lines))
    (tmp_path / "corpus-v2.jsonl").write_text(json.dumps({"name": "f", "status": "unsupported", "reason": "x",
                                                          "restriction": "rowid-alias"}) + "\n")
    assert costs(tmp_path) == {
        "cases": {"corpus-v1": 5, "corpus-v2": 1},
        "restrictions": {"real-value": 2, "rowid-alias": 1},
        "frontend": {"This statement is not modeled": 1},
        "undeclared": {"out of scope without a refusal": 1}}
