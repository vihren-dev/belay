"""Test of the local build loop, the recipes `just dev-build` and `just dev-verdict`.

It runs the recipes in the shell of `shell.nix`, and skips outside it.
"""

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]


def just(*arguments: str, timeout: int) -> subprocess.CompletedProcess[str]:
    """Run a recipe in the repository and keep its output for the assertion messages."""
    return subprocess.run(["just", *arguments], cwd=ROOT, capture_output=True, text=True, timeout=timeout,
                          check=False)


@pytest.mark.requires_nix
def test_local_loop_builds_incrementally_and_runs_the_judge() -> None:
    """In the shell of `shell.nix`: `just dev-build` compiles nothing on a second run, the
    programs it links start (a Lean upgrade that changes the flags of the `LEAN_CC` wrapper
    fails here), and `just dev-verdict` on one small corpus checks only that corpus's claim,
    with the programs at the paths that `conformance.predict` reads, and exits with 0."""
    needed = ["BELAY_PARSER_LIBRARY", *(["LEAN_CC"] if sys.platform.startswith("linux") else [])]
    missing = [name for name in needed if not os.environ.get(name)]
    if missing:
        pytest.skip(f"{', '.join(missing)} not set: not the shell of shell.nix")
    first = just("dev-build", timeout=1200)
    assert first.returncode == 0, first.stdout[-4000:] + first.stderr[-4000:]
    second = just("dev-build", timeout=300)
    assert second.returncode == 0, second.stdout[-4000:] + second.stderr[-4000:]
    assert "Built " not in second.stdout, second.stdout[-4000:]
    for package, target in (("belay-sqlite-text", "belay-sqlite-translate"),
                            ("verifier-conformance", "conformance-runner")):
        program = ROOT / "packages" / package / ".lake/build/bin" / target
        started = subprocess.run([str(program)], input="", capture_output=True, text=True, timeout=60, check=False)
        assert started.returncode == 0, f"{program}: {started.returncode} {started.stderr[-2000:]}"
    judged = just("dev-verdict", "corpus-v10", timeout=600)
    assert judged.returncode == 0, judged.stdout[-4000:] + judged.stderr[-4000:]
    report = json.loads((ROOT / "build/dev/report.json").read_text(encoding="utf-8"))
    assert list(report) == ["corpus-v10"]
