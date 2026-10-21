"""Release requirement identities, frozen progress, and measured-coverage report boundaries."""

import hashlib
import json
from pathlib import Path
import struct

import pytest
from conformance.corpus import load, native_replay
from conformance.measure_coverage import gcov_counts
from conformance.native_connection import Connection, library_path, load_library
from conformance.native_replay import schema_sql
from conformance.progress import loaded_progress, progress
from conformance.sql_text import runtime_translator

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("parser-library", "sqlite3")]


def test_release_requirement_ids() -> None:
    """The full upstream requirement IDs must hash their exact normalized text."""
    inventory = json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text())
    assert inventory["count"] == len(inventory["requirements"]) == 3500
    for row in inventory["requirements"]:
        digest = hashlib.md5(row["text"].encode()).digest()
        assert row["id"] == "R-" + "-".join(f"{value:05d}" for value in struct.unpack(">8H", digest))


def test_frozen_progress_and_replay(runtime_root: Path, tmp_path: Path) -> None:
    """V2 extends v1 without changing its evidence, and indexed schemas replay in dependency order."""
    _, original = load(ROOT / "conformance/corpus-v1")
    manifest, records = load(ROOT / "conformance/corpus-v2")
    assert records[:len(original)] == original and len(records) == 183
    native_replay(records[len(original):])
    for record in records[len(original):]:
        connection = Connection(load_library(library_path()), tmp_path / (record["name"] + ".db"))
        try:
            connection.execute_script(schema_sql(record["initial"]["visible"]))
        finally:
            connection.close()
    report = progress(ROOT / "conformance/corpus-v2", ROOT / "conformance/requirements-3.51.0.json", runtime_root)
    assert sum(report["counts"].values()) == manifest["recordedCases"]
    inventory = json.loads((ROOT / "conformance/requirements-3.51.0.json").read_text())
    assert report["requirementMatrixRows"] == inventory["count"] == 3500
    assert [row["id"] for row in report["requirementMatrix"]] == [row["id"] for row in inventory["requirements"]]
    assert any(sum(row["counts"].values()) == 0 for row in report["requirementMatrix"])


def test_gcov_reached_function_denominator() -> None:
    """Untaken arcs in reached functions count; unreachable functions do not inflate this scope."""
    report = gcov_counts("function reached called 2 returned 100% blocks executed 50%\n"
        "branch 0 taken 2\nbranch 1 taken 0\nbranch 2 never executed\n"
        "function unreached called 0 returned 0% blocks executed 0%\nbranch 0 never executed\n")
    assert report["functionsReached"] == 1 and report["functionsInReport"] == 2
    assert report["branchesTaken"] == 1 and report["branchesInReachedFunctions"] == 3


def test_parser_failure_is_not_subset_exclusion(runtime_root: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A broken parser cannot turn a frozen native case into an unsupported verdict."""
    from conformance.native_replay import prepare
    from conformance.sql_text import Translator
    record = load(ROOT / "conformance/corpus-v2")[1][-1]
    def failed(*args: object, **kwargs: object) -> dict[str, object]:
        """Inject the translation program's answer for an unusable parse document of the library."""
        return {"result": "error", "message": "the parser library's parse document is not usable: injected"}
    monkeypatch.setattr(Translator, "answer", failed)
    assert prepare(record, runtime_translator(runtime_root))[1]["verdict"] == "HARNESS_ERROR"


def test_review_corpus_extends_and_replays(runtime_root: Path) -> None:
    """`conformance.progress.loaded_progress` on corpus v3, which extends v2.

    V3 keeps the v2 records, its new cases replay natively, and the report
    covers more than 40 requirement rows and counts query-only blockers
    separately. The judge (`judge/claims.json`) states the verdicts.
    """
    import gzip
    _, previous = load(ROOT / "conformance/corpus-v2")
    manifest, records = load(ROOT / "conformance/corpus-v3")
    assert records[:len(previous)] == previous
    additions = records[len(previous):]
    assert manifest["addedAuthoredCases"] == 23
    assert len(additions) == manifest["addedAuthoredCases"] + manifest["addedUpstreamCases"]
    native_replay(additions)
    extraction = gzip.decompress((ROOT / "conformance/corpus-v3/extraction.json.gz").read_bytes())
    assert hashlib.sha256(extraction).hexdigest() == manifest["upstreamManifestSha256"]
    assert any(record.get("upstream", {}).get("file", "").startswith("e_") and record["requirements"] for record in additions)
    report = loaded_progress(ROOT / "conformance/corpus-v3", manifest, records,
                             ROOT / "conformance/requirements-3.51.0.json", runtime_root)
    assert sum(report["counts"].values()) == len(records)
    assert sum(any(row["counts"].values()) for row in report["requirementMatrix"]) > 40
    assert report["queryDiagnostics"]["QUERY_ONLY_CASE"] >= 4
    authored = {record["name"]: record for record in additions if "upstream" not in record}
    assert authored["numeric-text-integer"]["trace"][0]["visible"]["tables"][0]["rows"][0]["values"] == [{"integer": {"value": 1}}]
    assert authored["text-numeric-conversion"]["trace"][0]["visible"]["tables"][0]["rows"][0]["values"] == [{"text": {"bytes": [52, 50]}}]
    assert authored["create-unique-duplicate"]["trace"][0]["primaryCode"] == 19


def test_parser_limit_on_a_natively_refused_migration_is_unsupported(runtime_root: Path,
                                                                     monkeypatch: pytest.MonkeyPatch) -> None:
    """`native_replay.prepare` counts a migration over the parser's size limits as outside the
    model only when native SQLite refused it too; after a native success it is a harness error."""
    import copy
    from conformance.native_replay import prepare
    from conformance.sql_text import TextParser, Translation
    record = load(ROOT / "conformance/corpus-v2")[1][-1]
    translate = TextParser.translate

    def limited(parser: TextParser, sql: bytes, source: str) -> Translation:
        """Stop at the parser's size limit for the migration only, as the program answers."""
        if source == "corpus-migration.sql":
            return Translation({"result": "limit", "refusal": {"status": "UNVERIFIED", "message": "limit",
                                                                "source": source, "start": 0, "end": 0}})
        return translate(parser, sql, source)
    monkeypatch.setattr(TextParser, "translate", limited)
    translator = runtime_translator(runtime_root)
    assert record["trace"][-1]["primaryCode"] == 0
    assert prepare(record, translator)[1]["verdict"] == "HARNESS_ERROR"
    refused = copy.deepcopy(record)
    refused["trace"][-1]["primaryCode"] = 1
    assert prepare(refused, translator)[1]["verdict"] == "MODEL_UNSUPPORTED"
