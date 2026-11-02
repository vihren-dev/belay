"""The committed generated C of the parser library equals a fresh generation.

These tests check `parser/generated/`, which `just parser-sources` writes from the tree that
`parserLibrary.generated` in `build-support/parser-library.nix` builds (ADR 0023, D1 and D3).
Lake compiles the committed files, so only this check ties them to the vendored SQLite
sources, their hash checks and the generators. The runtime root is the fresh tree.
"""

import json
from pathlib import Path

import pytest

pytestmark = [pytest.mark.integration, pytest.mark.parser]
COMMITTED = Path(__file__).resolve().parents[1] / "parser" / "generated"
"""The committed tree, in the source tree that holds this test."""


def files_under(directory: Path) -> dict[str, bytes]:
    """The bytes of each file under directory, by its path relative to directory."""
    return {path.relative_to(directory).as_posix(): path.read_bytes()
            for path in sorted(directory.rglob("*")) if path.is_file()}


def differences(committed: dict[str, bytes], fresh: dict[str, bytes]) -> list[str]:
    """One line for each file that is missing, extra or different, with the file's name."""
    return ([f"{name}: committed, but the generation does not write it" for name in sorted(committed.keys() - fresh.keys())]
            + [f"{name}: the generation writes it, but it is not committed" for name in sorted(fresh.keys() - committed.keys())]
            + [f"{name}: the committed bytes differ from the generation"
               for name in sorted(committed.keys() & fresh.keys()) if committed[name] != fresh[name]])


@pytest.mark.timeout(60)
def test_committed_files_equal_a_fresh_generation(runtime_root: Path) -> None:
    """Each file under `parser/generated/` is byte-identical to the file of the same name that
    the Nix generation writes, and neither side has a file that the other lacks. A failure names each
    file; run `just parser-sources` and commit the result."""
    found = differences(files_under(COMMITTED), files_under(runtime_root))
    assert not found, "parser/generated differs from the generation (run `just parser-sources`):\n" + "\n".join(found)


@pytest.mark.timeout(60)
def test_manifest_names_one_folder_for_each_grammar() -> None:
    """The manifest lists a folder for each grammar, named by the digits of its symbol prefix,
    and every folder of the tree is listed. The Lake build of the text package reads these folders."""
    manifest = json.loads((COMMITTED / "manifest.json").read_text())
    folders = {grammar["folder"] for grammar in manifest["grammars"]}
    assert all(grammar["prefix"] == "Syntax_" + grammar["folder"] for grammar in manifest["grammars"])
    assert folders == {path.name for path in COMMITTED.iterdir() if path.is_dir()}
