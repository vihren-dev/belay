"""`just build` links the Lean outputs of the built runtime into the checkout.

Tests that use the checkout as their runtime root read the compiled modules where
the installed runtime has them (see `tests/runtime_fixtures.py`): the verifier
library's at `.lake/build`, and each shipped package's at `packages/NAME/.lake/build`.
`build-support/runtime.nix` decides which packages the runtime ships. Without the
link of a new shipped package, those tests fail with a missing module file although
the runtime has it.
"""

from pathlib import Path
import re
import shlex
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.unit, pytest.mark.environment]


@pytest.mark.requires_native("just")
def test_build_links_each_runtime_lake_output() -> None:
    """The checkout gets a `.lake/build` link into `build/runtime` for the root and each shipped package."""
    result = subprocess.run(["just", "--dry-run", "build"], cwd=ROOT, capture_output=True,
                            text=True, timeout=5)
    assert result.returncode == 0, result.stdout + result.stderr
    links: dict[Path, Path] = {}
    for line in (result.stdout + result.stderr).splitlines():
        words = shlex.split(line)
        if words[:2] == ["ln", "-sfn"]:
            link = ROOT / words[3]
            links[link] = (link.parent / words[2]).resolve(strict=False)
    shipped = re.findall(r'"\$out/(packages/[^"/]+)"', (ROOT / "build-support/runtime.nix").read_text())
    assert shipped, "build-support/runtime.nix ships no package; the test no longer reads it correctly"
    for relative in (Path("."), *map(Path, shipped)):
        link = ROOT / relative / ".lake/build"
        assert link in links, f"just build does not link {relative / '.lake/build'}"
        assert links[link] == (ROOT / "build/runtime" / relative / ".lake/build").resolve(strict=False)
