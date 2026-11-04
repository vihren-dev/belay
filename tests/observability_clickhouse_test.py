"""Check our exact uploader/schema contract against a disposable pinned ClickHouse server."""

import json
import os
from pathlib import Path
import socket
import subprocess
import time
import urllib.error
import urllib.request

import pytest

from tests.observability_support import observation
from tools.observability_upload import upload_pending

pytestmark = [pytest.mark.integration, pytest.mark.timeout(90)]
ROOT = Path(__file__).resolve().parents[1]
"""The schema export is an explicit Nix input, independent of Lean/conformance sources."""


def query(url: str, sql: str) -> str:
    """Run a bounded query against only the disposable local server."""
    with urllib.request.urlopen(urllib.request.Request(url, data=sql.encode()), timeout=2) as response:
        return response.read().decode().strip()


def test_immutable_replay_and_fresh_execution(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Our IDs, JSON encoding and FINAL views prevent immediate double counting after replay."""
    binary = os.environ["BELAY_TEST_CLICKHOUSE"]
    expected_version = os.environ["BELAY_TEST_CLICKHOUSE_VERSION"]
    version = subprocess.run([binary, "--version"], capture_output=True, text=True, check=True, timeout=5)
    assert expected_version.removesuffix("-lts") in version.stdout
    with socket.socket() as reserve:
        reserve.bind(("127.0.0.1", 0))
        port = reserve.getsockname()[1]
    config = tmp_path / "config.xml"
    config.write_text(f'''<clickhouse>
<logger><level>warning</level><console>1</console></logger>
<path>{tmp_path}/data/</path><tmp_path>{tmp_path}/tmp/</tmp_path>
<user_files_path>{tmp_path}/files/</user_files_path>
<format_schema_path>{tmp_path}/schemas/</format_schema_path>
<listen_host>127.0.0.1</listen_host><http_port>{port}</http_port>
<max_connections>32</max_connections><max_thread_pool_size>128</max_thread_pool_size>
<background_pool_size>2</background_pool_size>
<background_schedule_pool_size>2</background_schedule_pool_size>
<background_buffer_flush_schedule_pool_size>1</background_buffer_flush_schedule_pool_size>
<background_message_broker_schedule_pool_size>1</background_message_broker_schedule_pool_size>
<background_distributed_schedule_pool_size>1</background_distributed_schedule_pool_size>
<merge_tree><number_of_free_entries_in_pool_to_execute_mutation>1</number_of_free_entries_in_pool_to_execute_mutation>
<number_of_free_entries_in_pool_to_execute_optimize_entire_partition>1</number_of_free_entries_in_pool_to_execute_optimize_entire_partition>
<number_of_free_entries_in_pool_to_lower_max_size_of_merge>1</number_of_free_entries_in_pool_to_lower_max_size_of_merge></merge_tree>
<profiles><default><max_threads>2</max_threads></default></profiles>
<users><default><password></password><networks><ip>127.0.0.1</ip></networks>
<profile>default</profile><quota>default</quota></default></users>
<quotas><default><interval><duration>3600</duration></interval></default></quotas>
</clickhouse>''')
    url = f"http://127.0.0.1:{port}/"
    log = tmp_path / "server.log"
    with log.open("w") as output:
        process = subprocess.Popen([binary, "server", f"--config-file={config}"],
                                   stdout=output, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 30
            while True:
                try:
                    assert query(url, "SELECT 1") == "1"
                    break
                except (OSError, urllib.error.URLError):
                    assert process.poll() is None and time.monotonic() < deadline, log.read_text()
                    time.sleep(0.1)
            for statement in (ROOT / "build-support/observability-schema.sql").read_text().split(";"):
                if statement.strip():
                    query(url, statement)
            query(url, "SYSTEM STOP MERGES")
            monkeypatch.setenv("BELAY_CLICKHOUSE_URL", url)
            monkeypatch.setenv("BELAY_CLICKHOUSE_USER", "default")
            monkeypatch.setenv("BELAY_CLICKHOUSE_PASSWORD", "")
            pending = tmp_path / "pending"
            directory = observation(pending)
            assert upload_pending(pending)
            (directory / ".uploaded").unlink()
            assert upload_pending(pending)
            assert query(url, "SELECT count() FROM belay_observability.test_events_unique") == "1"
            assert query(url, "SELECT count() FROM belay_observability.test_executions_unique") == "1"
            row = json.loads(query(url, "SELECT * FROM belay_observability.test_events_unique FORMAT JSONEachRow"))
            assert row["test_node_id"].endswith("::test_case[param]")
            assert json.loads(row["data"])["future"] == {"value": 7}
            observation(pending)
            assert upload_pending(pending)
            assert query(url, "SELECT count() FROM belay_observability.test_events_unique") == "2"
            assert query(url, "SELECT count() FROM belay_observability.test_executions_unique") == "2"
        finally:
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)
