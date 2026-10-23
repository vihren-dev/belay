"""What the editor shows for a file that uses the parser library (ADR 0017, S1, prototype 1).

The script is a small language server client: it starts `lake serve` in the surface package,
opens one Lean file, and prints the diagnostics that the server published when it answers
Lean's `textDocument/waitForDiagnostics` request for that version of the file, which it does
after it has published all of them, with the seconds from opening it. The editor's Lean
extension starts the same server and shows the same diagnostics.

Run from the repository root: `python3 experiments/surface-s1/editor.py PACKAGE FILE`, where
PACKAGE is a built, writable copy of `packages/belay` and FILE a Lean file in it. The
environment needs `lake` on the path and `BELAY_PARSER_LIBRARY`, as `packages/belay/README.md`
says.
"""

import json
from pathlib import Path
import subprocess
import sys
from time import monotonic
from typing import IO

Json = None | bool | int | float | str | list["Json"] | dict[str, "Json"]
"""A decoded JSON value of the protocol."""


def send(stream: IO[bytes], message: dict[str, Json]) -> None:
    """Write one message with its `Content-Length` header."""
    body = json.dumps(message).encode()
    stream.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
    stream.flush()


def receive(stream: IO[bytes]) -> dict[str, Json]:
    """Read one message."""
    length = 0
    while (line := stream.readline().decode().strip()):
        if line.lower().startswith("content-length:"):
            length = int(line.split(":", 1)[1])
    return json.loads(stream.read(length))


def main() -> None:
    """Open the file, wait until the server has published its diagnostics, and print them."""
    package, source = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    server = subprocess.Popen(["lake", "serve"], cwd=package, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert server.stdin is not None and server.stdout is not None
    send(server.stdin, {"jsonrpc": "2.0", "id": 1, "method": "initialize",
                        "params": {"processId": None, "rootUri": package.as_uri(), "capabilities": {}}})
    while receive(server.stdout).get("id") != 1:
        pass
    send(server.stdin, {"jsonrpc": "2.0", "method": "initialized", "params": {}})
    started = monotonic()
    send(server.stdin, {"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
        "uri": source.as_uri(), "languageId": "lean4", "version": 1, "text": source.read_text()}}})
    send(server.stdin, {"jsonrpc": "2.0", "id": 3, "method": "textDocument/waitForDiagnostics",
                        "params": {"uri": source.as_uri(), "version": 1}})
    diagnostics: list[Json] = []
    while (message := receive(server.stdout)).get("id") != 3:
        params = message.get("params")
        if message.get("method") == "textDocument/publishDiagnostics" and isinstance(params, dict):
            diagnostics = params["diagnostics"]  # type: ignore[assignment]
    elapsed = monotonic() - started
    for diagnostic in diagnostics:
        assert isinstance(diagnostic, dict)
        start = diagnostic["range"]["start"]  # type: ignore[index]
        print(f"{start['line'] + 1}:{start['character']} severity {diagnostic['severity']}: "  # type: ignore[index]
              f"{str(diagnostic['message']).splitlines()[0]}")
    print(f"processed in {elapsed:.2f} s")
    send(server.stdin, {"jsonrpc": "2.0", "id": 2, "method": "shutdown", "params": None})
    send(server.stdin, {"jsonrpc": "2.0", "method": "exit", "params": None})
    server.wait(timeout=30)


if __name__ == "__main__":
    main()
