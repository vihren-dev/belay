"""Small real HTTP and pytest fixtures for our artifact and delivery integration."""

from collections.abc import Iterator
from contextlib import contextmanager
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import shutil
import socket
import threading
from uuid import uuid4

ROOT = Path(__file__).resolve().parents[1]
"""Source files copied into isolated test repositories."""


def observation(root: Path) -> Path:
    """Write one representative report with a future field and no required metadata."""
    identity = str(uuid4())
    directory = root / identity
    directory.mkdir(parents=True)
    (directory / "execution.json").write_text(json.dumps({"execution_id": identity,
        "started_at": "2026-11-04T12:00:00.123456+00:00", "metadata": {}}))
    (directory / "report.jsonl").write_text(json.dumps({"$report_type": "FutureEvent",
        "nodeid": "tests/test_example.py::test_case[param]", "future": {"value": 7}}) + "\n")
    return directory


def harness(root: Path) -> Path:
    """Copy the actual shared setup without a conformance runtime or other tests."""
    root.mkdir(parents=True)
    for name in ("pytest.ini", "conftest.py"):
        shutil.copyfile(ROOT / name, root / name)
    for package, names in {
        "tests": ["__init__.py", "runtime_fixtures.py", "runtime_support.py"],
        "tools": ["__init__.py", *(path.name for path in (ROOT / "tools").glob("observability_*.py"))],
    }.items():
        (root / package).mkdir()
        for name in names:
            shutil.copyfile(ROOT / package / name, root / package / name)
    (root / "tests/test_discovered.py").write_text('''import pytest
@pytest.mark.parametrize("value", [1, 2])
def test_discovered(value):
    """A new test automatically inherits the repository's reporting integration."""
    assert value == 1
''')
    return root


def environment(spool: Path, url: str = "") -> dict[str, str]:
    """Isolate test children from real database credentials and any outer Nix build mode."""
    result = {key: value for key, value in os.environ.items()
              if not key.startswith(("BELAY_CLICKHOUSE_", "BELAY_OBSERVABILITY_"))}
    result.update(BELAY_OBSERVABILITY_SPOOL=str(spool), BELAY_CLICKHOUSE_URL=url,
                  PYTEST_DISABLE_PLUGIN_AUTOLOAD="1")
    return result


@contextmanager
def receiver(*, lose_acknowledgement: bool = False) -> Iterator[tuple[str, list[dict[str, object]]]]:
    """Receive real inserts; optionally drop one acknowledgement after accepting an event batch."""
    rows: list[dict[str, object]] = []
    remaining_loss = lose_acknowledgement

    class Handler(BaseHTTPRequestHandler):
        """A controlled server that records data and can model an uncertain insert acknowledgement."""

        def do_POST(self) -> None:
            """Accept the entire body before an optional connection loss."""
            nonlocal remaining_loss
            self.connection.settimeout(3)
            received = self.rfile.read(int(self.headers["Content-Length"]))
            rows.extend(json.loads(line) for line in received.splitlines())
            if remaining_loss and "test_events" in self.path:
                remaining_loss = False
                self.connection.shutdown(socket.SHUT_RDWR)
                self.connection.close()
                return
            self.send_response(200)
            self.send_header("Content-Length", "0")
            self.end_headers()

        def log_message(self, format: str, *args: object) -> None:
            """Keep fixture request logs out of pytest output."""

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    worker = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.05}, daemon=True)
    worker.start()
    try:
        yield f"http://127.0.0.1:{server.server_port}/", rows
    finally:
        server.shutdown()
        server.server_close()
        worker.join(timeout=3)
