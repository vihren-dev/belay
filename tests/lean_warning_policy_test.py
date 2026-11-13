"""Test of the warning policy of the Lean packages that a consumer project builds (issue #372).

A consumer project replays the warnings of each module of `belay-sqlite-model`, `belay-sqlite-text` and
`belay` in each of its own lake commands. The local build loop (`just dev-build`) and the Nix package
builds (`build-support/lean-package.nix`) run `lake build --wfail` for these packages, so a new warning
fails the build before it reaches a consumer.
"""

from pathlib import Path
import re
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
CONSUMER_PACKAGES = {"belay-sqlite-model": "modelPackage", "belay-sqlite-text": "textPackage", "belay": "surfacePackage"}
"""The package folders under `packages/` that a consumer project builds, and their Nix attributes."""


def test_dev_build_fails_on_warnings_of_consumer_packages() -> None:
    """The recipe `dev-build` of the justfile builds each consumer package with `lake build --wfail`."""
    justfile = (ROOT / "justfile").read_text()
    recipe = re.search(r"^dev-build:.*?\n((?:    .*\n)+)", justfile, re.MULTILINE)
    assert recipe is not None, "the justfile has no dev-build recipe"
    for folder in CONSUMER_PACKAGES:
        line = next((line for line in recipe.group(1).splitlines() if f"cd packages/{folder} &&" in line), None)
        assert line is not None, f"dev-build does not build packages/{folder}"
        assert "lake build --wfail " in line, f"dev-build builds packages/{folder} without --wfail: {line.strip()}"


@pytest.mark.requires_nix
@pytest.mark.parametrize(("folder", "attribute"), CONSUMER_PACKAGES.items())
def test_nix_build_fails_on_warnings_of_consumer_packages(folder: str, attribute: str) -> None:
    """The build phase of the Nix derivation of each consumer package runs `lake build --wfail`."""
    expression = f"(import {ROOT}/build-support/default.nix {{}}).{attribute}.buildPhase"
    result = subprocess.run(["nix-instantiate", "--eval", "--strict", "--json", "-E", expression],
                            capture_output=True, text=True, timeout=120, check=False)
    assert result.returncode == 0, result.stderr
    assert "lake build --no-ansi --wfail " in result.stdout, f"packages/{folder}: {result.stdout[-400:]}"
