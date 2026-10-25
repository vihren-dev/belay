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

    def __init__(self, runtime_root: Path, directory: Path, automatic_check: bool = False,
                 module: str = "_unknown",
                 extra_modules: dict[str, list[list[str]]] | None = None) -> None:
        """`module` names the fixture document's module; the server finds the file of a module in
        `directory` (LEAN_SRC_PATH), so a link to a location of the fixture or of a helper module resolves."""
        setup = module_setup(runtime_root, directory, automatic_check=automatic_check, module=module,
                             extra_modules=extra_modules)
        shim = directory / "lake-setup"
        shim.write_text(f"#!{sys.executable}\nimport pathlib, sys\n"
                        "assert sys.argv[1] == 'setup-file', sys.argv\n"
                        f"print(pathlib.Path({str(setup)!r}).read_text())\n")
        shim.chmod(0o755)
        self.directory = directory
        self.stderr = (directory / "server.stderr").open("wb")
        self.process = subprocess.Popen(
            [str(runtime_root / "lean/bin/lean"), "--server"], cwd=directory,
            env={**os.environ, "LAKE": str(shim), "LEAN_SRC_PATH": str(directory)}, stdin=subprocess.PIPE,
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

    def open(self, source: str, *, wait: bool = True) -> str:
        """Initialize one document; optionally await symbols. Background diagnostics need waitForDiagnostics."""
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
        if wait:
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


def compile_helper_module(runtime_root: Path, directory: Path, name: str, source: str) -> dict[str, list[list[str]]]:
    """Compile a fixture module that imports `Belay` to an `.olean` in `directory`, and give the
    import artifacts that `LeanServer` takes in `extra_modules`. The module keeps its own name, so a
    location in it links to `directory/<name>.lean`."""
    file = directory / f"{name}.lean"
    file.write_text(source)
    olean = directory / f"{name}.olean"
    (directory / "helper-setup").mkdir(exist_ok=True)
    setup = module_setup(runtime_root, directory / "helper-setup", module=name)
    result = subprocess.run([str(runtime_root / "lean/bin/lean"), f"--setup={setup}", "-o", str(olean), str(file)],
                            cwd=directory, timeout=120, capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    return {name: [[str(olean)]]}


def position(source: str, spelling: str, occurrence: int = 0) -> dict[str, int]:
    """Locate an exact fixture occurrence in LSP UTF-16 units, including non-BMP and CRLF."""
    offset = -1
    for _ in range(occurrence + 1):
        offset = source.index(spelling, offset + 1)
    before = source[:offset]
    return {"line": before.count("\n"),
            "character": len(before.rsplit("\n", 1)[-1].encode("utf-16-le")) // 2}


def hover(server: LeanServer, uri: str, start: dict[str, int]) -> dict[str, object]:
    """Request the SQL occurrence itself rather than its surrounding Lean term."""
    result = server.request("textDocument/hover", {"textDocument": {"uri": uri}, "position": start})
    assert isinstance(result, dict), result
    return result


def table_hover(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int,
                token: str) -> str:
    """The hover text of one table occurrence; the hover range must be exactly the written token."""
    start = position(source, spelling, occurrence)
    result = hover(server, uri, start)
    contents = result["contents"]
    assert isinstance(contents, dict) and isinstance(contents["value"], str), result
    end = {**start, "character": start["character"] + len(token)}
    assert result["range"] == {"start": start, "end": end}, result
    return contents["value"]


def diagnostics(server: LeanServer, uri: str, version: int = 1) -> list[dict[str, object]]:
    """The diagnostics that the server published last for the document, after it finished the version."""
    server.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version}, timeout=90)
    published = [message["params"]["diagnostics"] for message in server.notifications
                 if message.get("method") == "textDocument/publishDiagnostics" and message["params"]["uri"] == uri]
    assert published, server.notifications
    return published[-1]


def semantic_tokens(server: LeanServer, uri: str) -> list[tuple[int, int, int, str]]:
    """Decode the real server's relative token positions and advertised legend."""
    result = server.request("textDocument/semanticTokens/full", {"textDocument": {"uri": uri}})
    assert isinstance(result, dict) and isinstance(result["data"], list), result
    data = result["data"]
    assert all(isinstance(item, int) for item in data) and len(data) % 5 == 0, data
    line, column = 0, 0
    tokens: list[tuple[int, int, int, str]] = []
    for i in range(0, len(data), 5):
        line_delta, column_delta, length, kind, _ = data[i:i + 5]
        line += line_delta
        column = column_delta if line_delta else column + column_delta
        tokens.append((line, column, length, server.legend[kind]))
    return tokens
