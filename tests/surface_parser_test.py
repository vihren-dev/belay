"""The surface package (`packages/belay`, ADR 0016, D1) reads SQL text with the SQLite parser
library while a Lean file elaborates (ADR 0017, S1, prototype 1).

The runtime root of the `surface` suite holds the built package, the model and the parser
library (`build-support/tests.nix`). Each test runs `lean` with the options that Lake's
`setup-file` gives the editor's server for a file that imports `Belay`: the shim library as a
dynamic library and the package's shared library as a plugin, which links the parser library.
"""

import os
from pathlib import Path
import shutil
import sys

import pytest

from tests.runtime_support import run_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/surface"
"""The Lean files that the tests elaborate."""
SUFFIX = ".dylib" if sys.platform == "darwin" else ".so"
"""The file suffix of a shared library on this platform."""


def surface_command(runtime_root: Path, source: Path, plugin: Path | None = None) -> list[str]:
    """The `lean` command for a file that imports `Belay`, with the libraries that Lake loads."""
    library = runtime_root / "packages/belay/.lake/build/lib"
    return [str(runtime_root / "lean/bin/lean"), f"--load-dynlib={library / ('libbelayParserShim' + SUFFIX)}",
            f"--plugin={plugin or library / ('libbelay_Belay' + SUFFIX)}", str(source)]


def lean_path(runtime_root: Path) -> dict[str, str]:
    """The environment with the surface's and the model's Lean libraries on the search path."""
    paths = [runtime_root / "packages/belay/.lake/build/lib/lean",
             runtime_root / "packages/belay-sqlite-model/.lake/build/lib/lean"]
    return {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, paths))}


def test_accepted_sql_shows_its_command_count(runtime_root: Path, tmp_path: Path) -> None:
    """`#sql_parse` (`Belay/Sqlite/ParseCommand.lean`) parses valid SQL in the Lean process and
    shows the number of commands that SQLite's grammar accepts, also under `EXPLAIN`."""
    result = run_command(surface_command(runtime_root, FIXTURES / "Accepted.lean"), cwd=tmp_path,
                         environment=lean_path(runtime_root), timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "SQLite's grammar accepts 3 commands" in result.stdout, result.diagnostic()


def test_grammar_error_is_at_its_position_in_the_text(runtime_root: Path, tmp_path: Path) -> None:
    """A grammar error of the parser library is an error at the byte of the SQL text where SQLite's
    grammar rejects it: `FORM` in `#sql_parse "SELECT * FORM t;"` is line 6, column 21."""
    result = run_command(surface_command(runtime_root, FIXTURES / "Rejected.lean"), cwd=tmp_path,
                         environment=lean_path(runtime_root), timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "Rejected.lean:6:21: error: SQLite's grammar rejects the SQL here" in result.stdout, result.diagnostic()


@pytest.mark.skipif(sys.platform != "linux", reason="patchelf changes the library path of Linux libraries only")
def test_missing_parser_library_is_a_load_error(runtime_root: Path, tmp_path: Path) -> None:
    """When the parser library is missing, `lean` stops with the loader's error, which names the
    library, instead of elaborating the file: a copy of the package's shared library whose
    library path is an empty folder stands for an installation without the parser library."""
    plugin = tmp_path / f"libbelay_Belay{SUFFIX}"
    shutil.copy(runtime_root / f"packages/belay/.lake/build/lib/libbelay_Belay{SUFFIX}", plugin)
    plugin.chmod(0o755)
    (tmp_path / "empty").mkdir()
    patch = run_command(["patchelf", "--set-rpath", str(tmp_path / "empty"), str(plugin)], cwd=tmp_path, timeout=30)
    assert patch.returncode == 0, patch.diagnostic()
    result = run_command(surface_command(runtime_root, FIXTURES / "Accepted.lean", plugin), cwd=tmp_path,
                         environment=lean_path(runtime_root), timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "error loading library, libsqlite-verifier-parser.so: cannot open shared object file" in \
        result.stdout + result.stderr, result.diagnostic()
