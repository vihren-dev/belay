"""The authored coverage cases of name resolution (`conformance.authored_resolution`, ADR 0008).

Each case is recorded natively as a version 5 record with the error phase of each
statement, names requirement identifiers of the pinned documentation, and replays
through resolution and the execution semantics. The cases whose SQL the model
describes agree, including their error phases; the others stay out of scope.
"""

import json
from pathlib import Path

import pytest

from conformance.authored_resolution import definitions, records
from conformance.corpus import replay
from conformance.requirement_coverage import resolved_ids

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
OUT_OF_SCOPE = {"nonconstant-default", "add-not-null-to-rows", "multiple-primary-keys-neighbor",
                "nonconstant-default-neighbor"}
"""Cases whose SQL the model does not describe: a parenthesized default expression; a NOT
NULL column added to a table with rows, which SQLite reports in `sqlite3_step`; and a
CREATE TABLE that runs with a primary key or a default."""


def test_coverage_cases_record_phases_and_agree(runtime_root: Path) -> None:
    """Every case is a version 5 record with resolvable requirements and a phase on each error;
    all cases outside `OUT_OF_SCOPE` agree with the model, and none disagrees."""
    recorded = records()
    assert [record["name"] for record in recorded] == [case.name for case in definitions()]
    resolved_ids(recorded, json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text()))
    for record in recorded:
        assert record["nativeVersion"] == 5 and record["requirements"]
        assert all((event["phase"] is None) == (event["primaryCode"] == 0) for event in record["trace"])
    report = replay(recorded, runtime_root)
    assert report["counts"] == {"AGREE": len(recorded) - len(OUT_OF_SCOPE), "MODEL_UNSUPPORTED": len(OUT_OF_SCOPE)}
    phases = {record["name"]: record["trace"][-1]["phase"] for record in recorded}
    assert phases["commit-without-transaction"] == phases["add-not-null-to-rows"] == "step"
    assert phases["table-exists"] == phases["add-limit-before-duplicate"] == "prepare"


def test_coverage_corpus_round_trips(tmp_path: Path) -> None:
    """`conformance.resolution_evidence.publish` writes a corpus of version 5 records that reads
    back unchanged and replays natively, and refuses to replace an existing directory."""
    from conformance.corpus import load
    from conformance.resolution_evidence import publish
    manifest = publish(tmp_path / "corpus")
    assert manifest["nativeVersion"] == 5 and manifest["corpusVersion"] == 6
    assert manifest["recordedCases"] == len(definitions())
    assert load(tmp_path / "corpus")[0] == manifest
    with pytest.raises(ValueError, match="already exists"):
        publish(tmp_path / "corpus")
