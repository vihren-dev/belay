"""Write the `lakefile.toml` of the installed runtime from the verifier library package's (ADR 0010).

Usage: python3 library_lakefile.py PACKAGE_LAKEFILE > lakefile.toml

The installed runtime is a Lake package that users' proofs projects and the
verifier's own workspaces require by path. Lake replays its prebuilt outputs only
when its lakefile describes the same libraries that built them, so the libraries
come from `packages/sqlite-verifier/lakefile.toml` instead of a second copy. Two
things change: each requirement points to where the runtime ships it, and the
artifact cache is off, because the outputs are read-only and Lake must not copy
them into a user's cache.
"""

import json
from pathlib import Path
import sys
import tomllib

RUNTIME_PATHS = {"belaySqlite": "packages/belay-sqlite"}
"""Requirement name to its folder in the installed runtime."""


def library_lakefile(package: dict[str, object]) -> str:
    """The runtime's lakefile text for a parsed library package lakefile."""
    requirements = [entry for entry in package.get("require", []) if isinstance(entry, dict)]
    unknown = [entry.get("name") for entry in requirements if entry.get("name") not in RUNTIME_PATHS]
    if unknown or package.get("lean_exe"):
        raise SystemExit(f"The library package needs {unknown or 'executables'}, which the installed runtime does "
                         "not ship; add the requirement to RUNTIME_PATHS, or move the executables to another package.")
    lines = [f"name = {json.dumps(package['name'])}", f"version = {json.dumps(package['version'])}",
             "enableArtifactCache = false"]
    for requirement in requirements:
        lines += ["", "[[require]]", f"name = {json.dumps(requirement['name'])}",
                  f"path = {json.dumps(RUNTIME_PATHS[str(requirement['name'])])}"]
    for library in package.get("lean_lib", []):
        lines += ["", "[[lean_lib]]", *(f"{key} = {json.dumps(value)}" for key, value in library.items())]
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.stdout.write(library_lakefile(tomllib.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))))
