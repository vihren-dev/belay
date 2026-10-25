"""The public `sql` documentation block (`Belay/Sqlite/SqlDocBlock.lean`) checks SQL examples while a
file that imports `Belay` elaborates (ADR 0017, checked SQL documentation).

Each fixture under `tests/surface` holds cases. A case starts with a line `--! case NAME`, and the
lines `--! error LINE:COLUMN TEXT` after it state each error that Lean must report for the case:
LINE counts from the `--! case` line, COLUMN counts Unicode characters, and TEXT must be in the
message. A case without `--! error` lines must elaborate without any error or warning. One `lean`
run elaborates a whole fixture, and each case is a separate test.
"""

from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import sys

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, SUFFIX, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

FIXTURE_NAMES = ("SqlDocCasesText", "SqlDocCasesTyped", "SqlDocCasesBindings", "SqlDocCasesExplicit",
                 "SqlDocCasesFailures", "SqlDocCasesComments")
"""The fixtures with cases, without the suffix `.lean`."""
DIAGNOSTIC = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<column>\d+): (?P<kind>error|warning)(\([^)]*\))?: (?P<text>.*)$")
"""One diagnostic header line of `lean`; the lines after it belong to the message."""


@dataclass(frozen=True)
class Case:
    """One case of a fixture: its first line, and the errors that it must report as
    (line offset, column, message text)."""

    name: str
    first_line: int
    errors: tuple[tuple[int, int, str], ...]


def read_cases(text: str) -> list[Case]:
    """The cases of a fixture, in file order."""
    cases: list[Case] = []
    for number, line in enumerate(text.splitlines(), start=1):
        if line.startswith("--! case "):
            cases.append(Case(line.removeprefix("--! case ").strip(), number, ()))
        elif line.startswith("--! error "):
            position, _, message = line.removeprefix("--! error ").partition(" ")
            row, _, column = position.partition(":")
            last = cases[-1]
            cases[-1] = Case(last.name, last.first_line, last.errors + ((int(row), int(column), message),))
    return cases


def read_diagnostics(output: str) -> list[tuple[int, int, str]]:
    """The errors and warnings of `lean` output as (line, column, whole message)."""
    found: list[list[object]] = []
    for line in output.splitlines():
        match = DIAGNOSTIC.match(line)
        if match:
            found.append([int(match["line"]), int(match["column"]), match["text"]])
        elif found and not re.match(r"^\S+:\d+:\d+: ", line):
            found[-1][2] = f"{found[-1][2]}\n{line}"
    return [(int(row), int(column), str(text)) for row, column, text in found]


def elaborate(runtime_root: Path, directory: Path, text: str, name: str) -> list[tuple[int, int, str]]:
    """Elaborate the text as a file and give its errors and warnings. The text must make `lean` stop
    only because of errors."""
    directory.mkdir(parents=True, exist_ok=True)
    source = directory / f"{name}.lean"
    source.write_bytes(text.encode())
    result = run_command(surface_command(runtime_root, source, directory), cwd=directory, timeout=180)
    assert not result.timed_out, result.diagnostic()
    diagnostics = read_diagnostics(result.stdout + result.stderr)
    assert (result.returncode == 0) == (not diagnostics), result.diagnostic()
    return diagnostics


@pytest.fixture(scope="module", params=[False, True], ids=["lf", "crlf"])
def results(request: pytest.FixtureRequest, runtime_root: Path,
            tmp_path_factory: pytest.TempPathFactory) -> dict[str, list[tuple[int, int, str]]]:
    """The diagnostics of each fixture, with the line ends of the file as Unix or as Windows."""
    found: dict[str, list[tuple[int, int, str]]] = {}
    for name in FIXTURE_NAMES:
        text = (FIXTURES / f"{name}.lean").read_text()
        text = text.replace("\n", "\r\n") if request.param else text
        found[name] = elaborate(runtime_root, tmp_path_factory.mktemp(name), text, name)
    return found


CASES = [(name, case) for name in FIXTURE_NAMES for case in read_cases((FIXTURES / f"{name}.lean").read_text())]


@pytest.mark.parametrize(("fixture", "case"), CASES, ids=[f"{name}-{case.name}" for name, case in CASES])
def test_block_reports_exactly_its_stated_errors(results: dict[str, list[tuple[int, int, str]]], fixture: str,
                                                 case: Case) -> None:
    """The `sql` block expander reports the errors of a case at the stated positions of the
    original file, also after the file has Windows line ends, and no other error."""
    later = [other.first_line for other_name, other in CASES if other_name == fixture and other.first_line > case.first_line]
    end = min(later, default=10**9)
    actual = [(row - case.first_line, column, text) for row, column, text in results[fixture]
              if case.first_line <= row < end]
    assert [(row, column) for row, column, _ in actual] == [(row, column) for row, column, _ in case.errors], actual
    for (_, _, found), (_, _, wanted) in zip(actual, case.errors):
        assert wanted in found, f"{wanted!r} is not in {found!r}"


def test_no_error_is_outside_a_case(results: dict[str, list[tuple[int, int, str]]]) -> None:
    """Every error of a fixture belongs to a case, so an error of an import or of a helper
    definition cannot hide."""
    for fixture, diagnostics in results.items():
        first = min(case.first_line for name, case in CASES if name == fixture)
        assert [item for item in diagnostics if item[0] < first] == []


def case_text(fixture: str, name: str) -> tuple[str, str]:
    """The lines before the first case of a fixture, and the lines of the named case."""
    text = (FIXTURES / f"{fixture}.lean").read_text()
    parts = re.split(r"(?m)^(?=--! case )", text)
    return parts[0], next(part for part in parts[1:] if part.startswith(f"--! case {name}\n"))


@pytest.mark.parametrize(("name", "old", "new"), [
    ("matching-update-then-select", "-- 7", "-- 8"),
    ("matching-update-then-select", "SELECT x FROM t;\n-- 7", "SELECT x FROM t WHERE x = 8;\n-- 7"),
    ("matching-update-then-select", "UPDATE t SET x = 7", "UPDATE t SET x = 6"),
])
def test_mutating_a_passing_case_makes_it_fail(runtime_root: Path, tmp_path: Path, name: str, old: str, new: str) -> None:
    """A passing case elaborates, and the same case with a changed expected value or a changed SQL
    condition is an error of the block, so the check depends on both."""
    header, body = case_text("SqlDocCasesText", name)
    assert elaborate(runtime_root, tmp_path / "passing", header + body, "Passing") == []
    assert old in body
    mutated = elaborate(runtime_root, tmp_path / "mutated", header + body.replace(old, new), "Mutated")
    assert [text.splitlines()[0] for _, _, text in mutated] == ["SQL result mismatch"], mutated


@pytest.mark.skipif(sys.platform != "linux", reason="patchelf changes the library path of Linux libraries only")
def test_missing_parser_library_is_not_an_expected_failure(runtime_root: Path, tmp_path: Path) -> None:
    """Without the parser library, `lean` stops with the loader's error before it checks any block,
    also for a block with `+error` that expects a syntax error: an unavailable library is no SQL failure."""
    library = tmp_path / f"libbelaySqliteText_BelaySqliteText{SUFFIX}"
    shutil.copy(runtime_root / f"packages/belay/.lake/build/lib/libbelaySqliteText_BelaySqliteText{SUFFIX}", library)
    library.chmod(0o755)
    (tmp_path / "empty").mkdir()
    patch = run_command(["patchelf", "--set-rpath", str(tmp_path / "empty"), str(library)], cwd=tmp_path, timeout=30)
    assert patch.returncode == 0, patch.diagnostic()
    header, body = case_text("SqlDocCasesFailures", "syntax-error-is-an-expected-failure")
    source = tmp_path / "Syntax.lean"
    source.write_text(header + body)
    result = run_command(surface_command(runtime_root, source, tmp_path, library), cwd=tmp_path, timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "error loading library, libsqlite-verifier-parser.so: cannot open shared object file" in \
        result.stdout + result.stderr, result.diagnostic()
