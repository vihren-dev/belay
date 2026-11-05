"""Protect our shared reporting, spool, HTTP and artifact boundary with representative observations."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
from time import monotonic
from uuid import UUID, uuid5
import zipfile

import pytest

from tests.observability_support import environment, harness, observation, receiver
from tools.observability_ci import import_archive
from tools.observability_logs import export_reports, recover
from tools.observability_nix import run
from tools.observability_records import events, execution
from tools.observability_spool import attempt_upload, import_execution, lock
from tools.observability_upload import upload_pending

pytestmark = [pytest.mark.integration, pytest.mark.timeout(30)]


def test_native_reporting_finalizes_failed_concurrent_sessions(tmp_path: Path) -> None:
    """Fresh discovered tests inherit reporting/upload, including failures, without sharing identities."""
    root = harness(tmp_path / "repo")
    spool = tmp_path / "spool"
    with receiver() as (url, rows):
        def invoke() -> subprocess.CompletedProcess[str]:
            """Run one ordinary pytest command with no reportlog arguments."""
            return subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=root,
                                  env=environment(spool, url), capture_output=True, text=True, timeout=20)
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda _: invoke(), range(2)))
    assert all(result.returncode == 1 for result in results), results
    manifests = list(spool.glob("*/execution.json"))
    assert len(manifests) == 2
    identities = {execution(path.parent)["execution_id"] for path in manifests}
    assert len(identities) == 2
    assert all((path.parent / ".uploaded").exists() for path in manifests)
    reports = [json.loads(str(row["data"])) for row in rows if row.get("kind") == "TestReport"]
    assert {row["nodeid"] for row in reports} == {
        "tests/test_discovered.py::test_discovered[1]", "tests/test_discovered.py::test_discovered[2]"}
    assert {row["when"] for row in reports} == {"setup", "call", "teardown"}
    assert all(isinstance(row["duration"], (int, float)) for row in reports)
    assert any(row["outcome"] == "failed" for row in reports)
    assert {json.loads(str(row["data"]))["exitstatus"] for row in rows
            if row.get("kind") == "SessionFinish"} == {1}


def test_nested_pytest_inherits_the_persistent_spool(tmp_path: Path) -> None:
    """Copied subprocess harnesses keep pending reports alongside their caller's observations."""
    root = harness(tmp_path / "parent")
    nested = harness(tmp_path / "nested")
    (root / "tests/test_discovered.py").write_text(
        'import subprocess, sys\ndef test_child():\n'
        '    """Exercise an isolated repository pytest subprocess."""\n'
        f'    result = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd={str(nested)!r}, timeout=15)\n'
        '    assert result.returncode == 1\n')
    env = environment(tmp_path / "unused")
    del env["BELAY_OBSERVABILITY_SPOOL"]
    result = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=root, env=env,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0, result.stdout + result.stderr
    assert len(list((root / "build/observability").glob("*/execution.json"))) == 2
    assert not (nested / "build/observability").exists()


def test_replay_after_lost_acknowledgement_preserves_ids(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Our retry resends identical rows after uncertain delivery, and skips live producers."""
    directory = observation(tmp_path)
    monkeypatch.delenv("BELAY_OBSERVABILITY_BUILD", raising=False)
    with receiver(lose_acknowledgement=True) as (url, rows):
        monkeypatch.setenv("BELAY_CLICKHOUSE_URL", url)
        with lock(directory):
            assert upload_pending(tmp_path)
            assert rows == []
        assert not upload_pending(tmp_path)
        assert not (directory / ".uploaded").exists()
        assert upload_pending(tmp_path)
        assert (directory / ".uploaded").exists()
    native = [row for row in rows if row.get("kind") == "FutureEvent"]
    assert len(native) == 2 and native[0] == native[1]
    assert native[0]["event_id"] == str(uuid5(UUID(directory.name), "1"))
    assert json.loads(str(native[0]["data"]))["future"] == {"value": 7}
    assert all(row["metadata"] == "{}" for row in rows if "metadata" in row)


def test_partial_and_malformed_logs_are_distinct(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    """Stopped partial writes preserve preceding events; malformed complete lines remain diagnostic errors."""
    directory = observation(tmp_path)
    report = directory / "report.jsonl"
    original = report.read_bytes()
    report.write_bytes(original + b'{"unfinished":')
    assert len(list(events(directory, directory.name))) == 1
    assert "unterminated" in capsys.readouterr().err
    report.write_bytes(original + b'not JSON\n')
    with pytest.raises(ValueError):
        list(events(directory, directory.name))
    assert report.read_bytes() == original + b'not JSON\n'


def test_build_log_and_ci_recovery_preserve_observations(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    """Our failed-builder frames and credential-free CI artifacts recover the same immutable session."""
    directory = observation(tmp_path / "builder")
    export_reports(directory.parent)
    frames = capsys.readouterr().out.splitlines()
    recover(frames + frames, tmp_path / "recovered")
    recovered = tmp_path / "recovered" / directory.name
    assert execution(recovered) == execution(directory)
    assert (recovered / "report.jsonl").read_bytes() == (directory / "report.jsonl").read_bytes()
    archive = tmp_path / "reports.zip"
    with zipfile.ZipFile(archive, "w") as zipped:
        for name in ("execution.json", "report.jsonl"):
            zipped.write(directory / name, f"nested/{directory.name}/{name}")
    import_archive(archive, tmp_path / "ci")
    assert execution(tmp_path / "ci" / directory.name) == execution(directory)
    import_execution(directory, tmp_path / "recovered")
    (directory / "report.jsonl").write_text("changed")
    with pytest.raises(ValueError, match="conflicting"):
        import_execution(directory, tmp_path / "recovered")
    with zipfile.ZipFile(archive, "w") as zipped:
        zipped.writestr("../execution.json", "{}")
    with pytest.raises(ValueError, match="path"):
        import_archive(archive, tmp_path / "ci")


def test_upload_worker_has_hard_deadline(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A blocked uploader is terminated without changing the caller's test outcome or deleting reports."""
    from tools import observability_spool
    directory = observation(tmp_path)
    monkeypatch.delenv("BELAY_OBSERVABILITY_BUILD", raising=False)
    monkeypatch.setattr(observability_spool, "UPLOAD_SECONDS", 0.01)
    started = monotonic()
    assert not attempt_upload(tmp_path)
    assert monotonic() - started < 2
    assert (directory / "report.jsonl").exists()


def test_explicit_upload_uses_bounded_worker(tmp_path: Path) -> None:
    """The diagnostic CLI shares automatic delivery's worker boundary and reports missing configuration."""
    directory = observation(tmp_path)
    result = subprocess.run([sys.executable, "-m", "tools.observability_upload", str(tmp_path)],
                            env=environment(tmp_path), capture_output=True, text=True, timeout=20)
    assert result.returncode == 1
    assert "BELAY_CLICKHOUSE_URL is unset" in result.stderr
    assert (directory / "report.jsonl").exists()


def test_host_runner_preserves_failure_and_recovers_logs(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]) -> None:
    """Our common Nix wrapper collects failed-builder frames without converting failure to success."""
    directory = observation(tmp_path / "builder")
    export_reports(directory.parent)
    frames = capsys.readouterr().out
    monkeypatch.setenv("BELAY_OBSERVABILITY_SPOOL", str(tmp_path / "host"))
    monkeypatch.delenv("BELAY_CLICKHOUSE_URL", raising=False)
    code = run([sys.executable, "-c", f"print({frames!r}); raise SystemExit(17)"], 5)
    assert code == 17
    assert execution(tmp_path / "host" / directory.name) == execution(directory)
    # An enclosing CI timeout must reach the Nix client as well as this wrapper.
    assert run([sys.executable, "-c", f"import os; assert os.getpgrp() == {os.getpgrp()}"], 5) == 0


def test_ci_credentials_are_separate_from_test_code() -> None:
    """Our workflow handles completed failures and nightly replay using main's code and artifacts as data."""
    root = Path(__file__).resolve().parents[1]
    tests = (root / ".github/workflows/ci.yml").read_text()
    uploader = (root / ".github/workflows/observability.yml").read_text()
    assert "BELAY_CLICKHOUSE_PASSWORD" not in tests
    assert tests.count("name: belay-observability-") == 2
    assert "types: [completed]" in uploader and "schedule:" in uploader
    assert "ref: main" in uploader and "head_sha" not in uploader
    assert "actions: read" in uploader and "environment: belay-observability" in uploader
    assert "python3 -m tools.observability_ci" in uploader


def test_schema_denial_retains_observations(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A schema permission failure prevents inserts and receipts, so the same files can retry."""
    directory = observation(tmp_path)
    with receiver(deny_schema=True) as (url, rows):
        monkeypatch.setenv("BELAY_CLICKHOUSE_URL", url)
        assert not upload_pending(tmp_path)
        assert rows == []
        assert not (directory / ".uploaded").exists()
    with receiver() as (url, rows):
        monkeypatch.setenv("BELAY_CLICKHOUSE_URL", url)
        assert upload_pending(tmp_path)
        assert len(rows) == 2
