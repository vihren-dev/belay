"""The surface package (`packages/belay`, ADR 0016, D1) reads SQL text with the SQLite parser
library while a Lean file elaborates (ADR 0017, S1, prototype 1).

Each test runs `lean` on a fixture with the libraries that Lake loads for it
(`tests/surface_support.py`).
"""

from pathlib import Path
import shutil
import sys

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, SUFFIX, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

def test_accepted_sql_shows_its_command_count(runtime_root: Path, tmp_path: Path) -> None:
    """`#sql_parse` (`Belay/Sqlite/ParseCommand.lean`) parses valid SQL in the Lean process and
    shows the number of commands that SQLite's grammar accepts, also under `EXPLAIN`."""
    result = run_command(surface_command(runtime_root, FIXTURES / "Accepted.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "SQLite's grammar accepts 3 commands" in result.stdout, result.diagnostic()


def test_grammar_error_is_at_its_position_in_the_text(runtime_root: Path, tmp_path: Path) -> None:
    """A grammar error of the parser library is an error at the byte of the SQL text where SQLite's
    grammar rejects it: `FORM` in `#sql_parse "SELECT * FORM t;"` is line 6, column 21."""
    result = run_command(surface_command(runtime_root, FIXTURES / "Rejected.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "Rejected.lean:6:21: error: SQLite's grammar rejects the SQL here" in result.stdout, result.diagnostic()


def test_grammar_selection_checks_elaborate(runtime_root: Path, tmp_path: Path) -> None:
    """The `#guard` checks of `selectGrammar` (`Belay/Sqlite/Grammar.lean`) hold: it finds the
    dialect without grammar options, and its errors end with what the user can do."""
    result = run_command(surface_command(runtime_root, FIXTURES / "GrammarChecks.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_bytes_that_are_not_utf8_are_a_grammar_error(runtime_root: Path, tmp_path: Path) -> None:
    """The binding (`Belay/Sqlite/ParserLibrary.lean`, `c/parser_shim.c` of the text package) passes
    the SQL as bytes: a byte 0xFF inside a string literal reaches the parser library, which checks
    that the whole text is UTF-8 before it tokenizes, and the result is a grammar error at offset 0."""
    result = run_command(surface_command(runtime_root, FIXTURES / "InvalidUtf8.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "invalid UTF-8: Belay.Sqlite.ParseResult.inputError 0" in result.stdout, result.diagnostic()


@pytest.mark.skipif(sys.platform != "linux", reason="patchelf changes the library path of Linux libraries only")
def test_missing_parser_library_is_a_load_error(runtime_root: Path, tmp_path: Path) -> None:
    """When the parser library is missing, `lean` stops with the loader's error, which names the
    library, instead of elaborating the file: a copy of the text package's shared library, which
    links the parser library, whose library path is an empty folder stands for an installation
    without the parser library."""
    library = tmp_path / f"libbelaySqliteText_BelaySqliteText{SUFFIX}"
    shutil.copy(runtime_root / f"packages/belay/.lake/build/lib/libbelaySqliteText_BelaySqliteText{SUFFIX}", library)
    library.chmod(0o755)
    (tmp_path / "empty").mkdir()
    patch = run_command(["patchelf", "--set-rpath", str(tmp_path / "empty"), str(library)], cwd=tmp_path, timeout=30)
    assert patch.returncode == 0, patch.diagnostic()
    result = run_command(surface_command(runtime_root, FIXTURES / "Accepted.lean", tmp_path, library), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "error loading library, libsqlite-verifier-parser.so: cannot open shared object file" in \
        result.stdout + result.stderr, result.diagnostic()
