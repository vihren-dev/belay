"""Test of the local build loop, the recipes `just dev-build` and `just dev-verdict`.

It runs the recipes in the shell of `shell.nix`, and skips outside it.
"""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

import pytest

from tests.parser_object_symbols import undeclared_calls

ROOT = Path(__file__).resolve().parents[1]
TEXT_PACKAGE = ROOT / "packages/belay-sqlite-text"
HEADER_WARNING = re.compile(r"file not found|implicit declaration|implicitly declar", re.IGNORECASE)
"""A compiler message that a declaration of `parser/c-headers` is missing."""


def just(*arguments: str, timeout: int) -> subprocess.CompletedProcess[str]:
    """Run a recipe in the repository and keep its output for the assertion messages."""
    return subprocess.run(["just", *arguments], cwd=ROOT, capture_output=True, text=True, timeout=timeout,
                          check=False)


@pytest.mark.requires_nix
def test_local_loop_builds_incrementally_and_runs_the_judge(tmp_path: Path) -> None:
    """In the shell of `shell.nix`, which sets `BELAY_DEV_SHELL`: `just dev-build` from a clean
    build folder of the text package compiles the parser's C with the declarations of
    `parser/c-headers` and no warning about a missing header or an implicit declaration, and the
    objects call only the reviewed C library functions; a second run compiles nothing; the programs
    it links start (a Lean upgrade that changes the flags of the `LEAN_CC` wrapper fails here);
    `lake lean` of a file that evaluates the parser library's metadata prints it; and
    `just dev-verdict` on one small corpus checks only that corpus's claim, with the programs at the
    paths that `conformance.predict` reads, and exits with 0."""
    needed = ["BELAY_DEV_SHELL", *(["LEAN_CC"] if sys.platform.startswith("linux") else [])]
    missing = [name for name in needed if not os.environ.get(name)]
    if missing:
        pytest.skip(f"{', '.join(missing)} not set: not the shell of shell.nix")
    shutil.rmtree(TEXT_PACKAGE / ".lake/build", ignore_errors=True)
    first = just("dev-build", timeout=1200)
    assert first.returncode == 0, first.stdout[-4000:] + first.stderr[-4000:]
    warnings = [line for line in (first.stdout + first.stderr).splitlines() if HEADER_WARNING.search(line)]
    assert not warnings, "\n".join(warnings)
    objects = sorted((TEXT_PACKAGE / ".lake/build/c/parser").glob("*.o"))
    assert len(objects) >= 3, objects
    calls = undeclared_calls(objects)
    assert not calls, f"review the declarations of these calls in parser/c-headers: {calls}"
    second = just("dev-build", timeout=300)
    assert second.returncode == 0, second.stdout[-4000:] + second.stderr[-4000:]
    assert "Built " not in second.stdout, second.stdout[-4000:]
    for package, target in (("belay-sqlite-text", "belay-sqlite-translate"),
                            ("verifier-conformance", "conformance-runner")):
        program = ROOT / "packages" / package / ".lake/build/bin" / target
        started = subprocess.run([str(program)], input="", capture_output=True, text=True, timeout=60, check=False)
        assert started.returncode == 0, f"{program}: {started.returncode} {started.stderr[-2000:]}"
    source = tmp_path / "Metadata.lean"
    source.write_text("import Belay.Sqlite.Frontend.Grammar.ParserLibrary\n#eval do IO.println (← Belay.Sqlite.ParserLibrary.metadata)\n",
                      encoding="utf-8")
    printed = subprocess.run(["lake", "lean", str(source)], cwd=TEXT_PACKAGE, capture_output=True, text=True,
                             timeout=300, check=False)
    assert printed.returncode == 0, printed.stdout[-4000:] + printed.stderr[-4000:]
    assert '{"api":' in printed.stdout and '"releases":' in printed.stdout, printed.stdout[-4000:]
    judged = just("dev-verdict", "corpus-v10", timeout=600)
    assert judged.returncode == 0, judged.stdout[-4000:] + judged.stderr[-4000:]
    report = json.loads((ROOT / "build/dev/report.json").read_text(encoding="utf-8"))
    assert list(report) == ["corpus-v10"]
