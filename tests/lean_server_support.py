"""Bounded Lean LSP sessions over the surface suite's installed module setup."""

import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import time

from tests.surface_support import module_setup


class LeanServer:
    """Run the real pinned server; a setup-file shim supplies our installed fixture artifacts."""

    def __init__(self, runtime_root: Path, directory: Path) -> None:
        setup = module_setup(runtime_root, directory)
        shim = directory / "lake-setup"
        shim.write_text(f"#!{sys.executable}\nimport pathlib, sys\n"
                        "assert sys.argv[1] == 'setup-file', sys.argv\n"
                        f"print(pathlib.Path({str(setup)!r}).read_text())\n")
        shim.chmod(0o755)
        self.directory = directory
        self.stderr = (directory / "server.stderr").open("wb")
        self.process = subprocess.Popen(
            [str(runtime_root / "lean/bin/lean"), "--server"], cwd=directory,
            env={**os.environ, "LAKE": str(shim)}, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=self.stderr, start_new_session=True)
        assert self.process.stdin is not None and self.process.stdout is not None
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.process.stdout, selectors.EVENT_READ)
        self.buffer = bytearray()
        self.serial = 0
        self.notifications: list[dict[str, object]] = []
        self.legend: list[str] = []

    def send(self, message: dict[str, object]) -> None:
        """Send one JSON-RPC frame; fixture messages fit in the server pipe buffer."""
        payload = json.dumps({"jsonrpc": "2.0", **message}).encode()
        assert self.process.stdin is not None
        self.process.stdin.write(f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload)
        self.process.stdin.flush()

    def receive(self, deadline: float) -> dict[str, object]:
        """Read one bounded frame, including fragmented headers and UTF-8 bodies."""
        while True:
            boundary = self.buffer.find(b"\r\n\r\n")
            if boundary >= 0:
                headers = self.buffer[:boundary].decode("ascii").split("\r\n")
                size = next(int(line.split(":", 1)[1]) for line in headers
                            if line.lower().startswith("content-length:"))
                end = boundary + 4 + size
                if len(self.buffer) >= end:
                    message = json.loads(self.buffer[boundary + 4:end])
                    del self.buffer[:end]
                    assert isinstance(message, dict), message
                    return message
            remaining = deadline - time.monotonic()
            assert remaining > 0 and self.selector.select(remaining), "Lean LSP response timed out"
            assert self.process.stdout is not None
            chunk = os.read(self.process.stdout.fileno(), 65536)
            assert chunk, (self.process.poll(), (self.directory / "server.stderr").read_text())
            self.buffer.extend(chunk)

    def request(self, method: str, params: dict[str, object], timeout: float = 45) -> object:
        """Await one response and retain notifications; acknowledge server refresh requests."""
        self.serial += 1
        request_id = self.serial
        self.send({"id": request_id, "method": method, "params": params})
        deadline = time.monotonic() + timeout
        while True:
            message = self.receive(deadline)
            if "method" in message:
                self.notifications.append(message)
                if "id" in message:
                    self.send({"id": message["id"], "result": None})
            elif message.get("id") == request_id:
                assert "error" not in message, message
                return message.get("result")

    def open(self, source: str) -> str:
        """Initialize and elaborate one document; documentSymbol waits for its full elaboration."""
        response = self.request("initialize", {"processId": os.getpid(),
            "rootUri": self.directory.as_uri(), "capabilities": {}})
        assert isinstance(response, dict)
        capabilities = response["capabilities"]
        assert isinstance(capabilities, dict)
        semantic = capabilities["semanticTokensProvider"]
        assert isinstance(semantic, dict) and isinstance(semantic["legend"], dict)
        token_types = semantic["legend"]["tokenTypes"]
        assert isinstance(token_types, list) and all(isinstance(item, str) for item in token_types)
        self.legend = token_types
        self.send({"method": "initialized", "params": {}})
        path = self.directory / "EditorFixture.lean"
        path.write_bytes(source.encode())
        uri = path.as_uri()
        self.send({"method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": uri, "languageId": "lean4", "version": 1, "text": source}}})
        self.request("textDocument/documentSymbol", {"textDocument": {"uri": uri}}, timeout=60)
        return uri

    def close(self) -> None:
        """Bound shutdown and kill only this server's process group if it cannot exit."""
        try:
            if self.process.poll() is None:
                self.request("shutdown", {}, timeout=5)
                self.send({"method": "exit"})
                self.process.wait(timeout=5)
        finally:
            if self.process.poll() is None:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait(timeout=5)
            self.selector.close()
            self.stderr.close()
            if self.process.stdin is not None:
                self.process.stdin.close()
            if self.process.stdout is not None:
                self.process.stdout.close()
