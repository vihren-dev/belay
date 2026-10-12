"""Write the library-only `lakefile.toml` of the installed runtime (ADR 0010 section 3).

Usage: python3 library_lakefile.py ROOT_LAKEFILE LIBRARY... > lakefile.toml

The installed runtime is a Lake package that users' proofs projects and the
verifier's own workspaces require by path. Lake replays its prebuilt outputs only
when its lakefile describes the same libraries that built them, so the libraries
come from the repository's own `lakefile.toml` instead of a second copy. The
result has no executables and no `lean4export` requirement, which the runtime
does not ship, and turns the artifact cache off: the outputs are read-only, and
Lake must not copy them into a user's cache.
"""

import json
from pathlib import Path
import sys
import tomllib

KEPT_REQUIREMENTS = frozenset({"belaySqlite"})
"""Requirements that the installed runtime ships next to its own outputs."""


def library_lakefile(root: dict[str, object], libraries: list[str]) -> str:
    """The library-only lakefile text for the named libraries of a parsed root lakefile."""
    declared = {entry["name"]: entry for entry in root.get("lean_lib", []) if isinstance(entry, dict)}
    missing = [name for name in libraries if name not in declared]
    if missing:
        raise SystemExit(f"Libraries {missing} are not declared in the root lakefile.toml; "
                         "name libraries that the root lakefile declares.")
    lines = [f"name = {json.dumps(root['name'])}", f"version = {json.dumps(root['version'])}",
             "enableArtifactCache = false"]
    for requirement in root.get("require", []):
        if isinstance(requirement, dict) and requirement.get("name") in KEPT_REQUIREMENTS:
            lines += ["", "[[require]]", f"name = {json.dumps(requirement['name'])}",
                      f"path = {json.dumps(requirement['path'])}"]
    for name in libraries:
        lines += ["", "[[lean_lib]]", f"name = {json.dumps(name)}"]
        for key in ("roots", "globs"):
            if key in declared[name]:
                lines.append(f"{key} = {json.dumps(declared[name][key])}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.stdout.write(library_lakefile(tomllib.loads(Path(sys.argv[1]).read_text(encoding="utf-8")), sys.argv[2:]))
