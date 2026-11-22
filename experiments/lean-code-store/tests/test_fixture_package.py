"""End-to-end test of the prototype on the fixture package `experiments/lean-code-store/fixture`.

It checks the folding rules, the user of a mention and the rows against `expected-rows.json`,
and the incremental behavior: a second run extracts nothing, and after an edit of one file only
that file and its importers are extracted. Set `LEAN_CODE_STORE_WRITE_EXPECTED=1` to rewrite the
expected file after a deliberate change; then read the difference before you commit it.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess

import pytest

from lean_code_store.run import run
from lean_code_store.store import LocalStore

pytestmark = [pytest.mark.requires_lean, pytest.mark.timeout(600)]

EXPERIMENT = Path(__file__).resolve().parents[1]
EXPECTED = EXPERIMENT / "fixture" / "expected-rows.json"
LAKE_TIMEOUT_SECONDS = 300


def _lake_build(directory: Path) -> None:
    """Build a Lake package; a failure shows Lake's output, which names the failing file."""
    result = subprocess.run(["lake", "build"], cwd=directory, capture_output=True, text=True,
                            timeout=LAKE_TIMEOUT_SECONDS)
    assert result.returncode == 0, f"lake build failed in {directory}:\n{result.stdout}{result.stderr}"


def _snapshot_rows(store: LocalStore, snapshot: str) -> dict[str, object]:
    """The rows of a snapshot without file keys, with the fold of each module, by module.

    References to Lean's library stay in: they show the folding of generated targets outside
    the project, for example `Nat.casesOn` into `Nat`.
    """
    files = [json.loads(line) for line in
             (store.root / "snapshots" / snapshot / "snapshot_files.jsonl").read_text().splitlines()]
    result: dict[str, object] = {}
    for file in files:
        version = store.version(file["file_key"])
        texts = {row["text_sha256"]: row["text"] for row in map(json.loads, (version / "entity_texts.jsonl").read_text().splitlines())}
        entities = [[row["name"], row["kind"], texts[row["text_sha256"]]]
                    for row in map(json.loads, (version / "entities.jsonl").read_text().splitlines())]
        references = [[row["user_module"], row["user_name"], row["target_module"], row["target_name"], row["kind"]]
                      for row in map(json.loads, (version / "entity_references.jsonl").read_text().splitlines())]
        result[file["module_name"]] = {"path": file["source_path"], "entities": entities,
                                       "references": references, "fold": store.fold(file["file_key"])}
    return result


def _run(package: Path, store: LocalStore, reader: Path, work: Path) -> dict[str, object]:
    """One run of the prototype on the fixture package copy."""
    lean = Path(shutil.which("lean") or "lean")
    return run([(".", package, "Fixture")], [], store, lean, reader, 2, "fixture", work)


def test_fixture_rows_and_incremental_runs(tmp_path: Path) -> None:
    """Rows match the expected file; a second run extracts no file; an edit extracts its importers."""
    _lake_build(EXPERIMENT / "extractor")
    reader = EXPERIMENT / "extractor" / ".lake" / "build" / "bin" / "lean-code-store-facts"
    package = tmp_path / "fixture"
    shutil.copytree(EXPERIMENT / "fixture", package, ignore=shutil.ignore_patterns(".lake", "expected-rows.json"))
    _lake_build(package)
    store = LocalStore(tmp_path / "store")
    first = _run(package, store, reader, tmp_path / "work")
    rows = _snapshot_rows(store, str(first["snapshot_id"]))
    if os.environ.get("LEAN_CODE_STORE_WRITE_EXPECTED") == "1":
        EXPECTED.write_text(json.dumps(rows, indent=1, sort_keys=True) + "\n")
    assert rows == json.loads(EXPECTED.read_text())
    assert first["extracted"] == 5
    assert _run(package, store, reader, tmp_path / "work")["extracted"] == 0
    derive = package / "Fixture" / "Derive.lean"
    derive.write_text(derive.read_text() + "\n/-- An added declaration. -/\ndef added : Nat := 1\n")
    _lake_build(package)
    third = _run(package, store, reader, tmp_path / "work")
    assert third["extracted_modules"] == ["Fixture.Derive", "Fixture.Uses"]
