"""S5 replays original bound SQL and rejects unavailable or inconsistent evidence."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]


def replay_reports(runtime_root: Path, tmp_path: Path) -> dict[str, dict[str, object]]:
    """Compile/import our source annotations, then exercise the production replay boundary."""
    setup_path = module_setup(runtime_root, tmp_path)
    setup = json.loads(setup_path.read_text())
    for name in ("CounterexampleReplaySource", "CounterexampleReplay"):
        setup["name"] = name
        setup_path.write_text(json.dumps(setup))
        artifact = tmp_path / f"{name}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup_path}",
                              "-o", str(artifact), str(FIXTURES / f"{name}.lean")],
                             cwd=tmp_path, timeout=180)
        assert result.returncode == 0, result.diagnostic()
        setup["importArts"][name] = [[str(artifact)]]
    assert "replay trust and unavailable checks passed" in result.stdout, result.diagnostic()
    reports: dict[str, dict[str, object]] = {}
    for line in result.stdout.splitlines():
        if line.startswith("REPLAY:"):
            report = json.loads(line.removeprefix("REPLAY:"))
            assert isinstance(report, dict) and isinstance(report.get("name"), str)
            reports[report["name"]] = report
    assert len(reports) == 9, reports
    return reports


def native_replay(sqlite: str, text: object, directory: Path, name: str,
                  inspect: str = "") -> CommandResult:
    """Run exactly the emitted shell text; optional inspection checks its reconstructed state."""
    assert isinstance(text, str)
    source = directory / f"{name}.sql"
    source.write_text(text + inspect)
    return run_command([sqlite, "-batch", "-json", str(directory / f"{name}.db"),
                        f'.read "{source}"'], cwd=directory, timeout=10)


def model_cell(value: object) -> str | int | None:
    """Decode the fixture's model cells; BLOB/text bytes are observed through original hex SQL."""
    if value == "null":
        return None
    assert isinstance(value, dict)
    if "integer" in value:
        payload = value["integer"]
        assert isinstance(payload, dict) and isinstance(payload.get("value"), int)
        return payload["value"]
    payload = value["text"]
    assert isinstance(payload, dict) and isinstance(payload.get("bytes"), list)
    return bytes(payload["bytes"]).decode("utf-8")


def native_rows(text: str) -> list[list[object]]:
    """Read the shell's successive JSON arrays, which can span several lines."""
    rows: list[list[object]] = []
    decoder = json.JSONDecoder()
    while text.strip():
        result, end = decoder.raw_decode(text.lstrip())
        assert isinstance(result, list) and all(isinstance(row, dict) for row in result)
        rows.extend(list(row.values()) for row in result)
        text = text.lstrip()[end:]
    return rows


def test_replay_matches_pinned_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """Our emitted SQL recreates names/cells, uses actual bindings and preserves original
    observations. A shell helper table cannot turn a missing-table failure into success.
    The fixture also refuses clock/counter/unmodeled results, forged metadata and divergent
    compiled values, including after imported source annotations and explicit rebinding."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = replay_reports(runtime_root, tmp_path)
    for name in ("values", "parameters", "rebound", "numeric-parameters", "numeric-boundaries", "unbound"):
        report = reports[name]
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        assert result.returncode == 0 and not result.stderr, result.diagnostic()
        actual = native_rows(result.stdout)
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        expected = [[model_cell(cell) for cell in row] for output in outputs for row in output["rows"]]
        assert actual == expected, (name, actual, expected)
        assert isinstance(report["original"], str)
        assert all(piece.strip() in report["sql"] for piece in report["original"].split(";"))
    for name, error in (("overflow", "integer overflow"),):
        report = reports[name]
        assert report["outputs"] == [{"error": 1}], report
        assert ".parameter" not in report["sql"], report
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        assert result.returncode != 0 and error in result.stderr, result.diagnostic()
    assert ".parameter" not in reports["unbound"]["sql"]
    result = native_replay(sqlite, reports["unbound"]["sql"], tmp_path, "no-helper",
                           "SELECT count(*) FROM sqlite_parameters;\n")
    assert result.returncode != 0 and "no such table" in result.stderr, result.diagnostic()
    predicate = reports["predicate"]
    assert predicate["original"] is None and predicate["outputs"] == []
    result = native_replay(sqlite, predicate["sql"], tmp_path, "predicate",
                           'SELECT hex(x),hex(b),n FROM "t""q" ORDER BY n;\n')
    assert result.returncode == 0, result.diagnostic()
    assert [list(row.values()) for row in json.loads(result.stdout)] == [
        ["612762", "00FF", None], ["C3A6", "", 1], ["C386", "27", 2], ["610062", "FF00", 3]]
    result = native_replay(sqlite, reports["generated"]["sql"], tmp_path, "generated",
                           "SELECT rowid,a FROM plain;\n")
    assert result.returncode == 0 and json.loads(result.stdout) == [{"rowid": 1, "a": 7}], result.diagnostic()
