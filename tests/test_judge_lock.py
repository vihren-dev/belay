"""The judge lock (`nix/judge.nix`, `nix/judge.lock.json`), ADR 0011.

The lock makes a change to the judge, its claims, a claimed corpus or the native SQLite
oracle impossible without a change to the code-owned lock file. These tests change one byte
of each part in a temporary copy of the repository, with corpus v1 as the only claim, and
check that Nix evaluation stops and names that part, and passes again when it is restored.
"""

import json
from pathlib import Path
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
NIX_TIMEOUT_SECONDS = 120
"""One evaluation of the lock over a small copy."""
COPIED = ["nix/judge.nix", "nix/sqlite.nix", "nix/flake.lock", "judge",
          "conformance/corpus-v1"]
"""The files that the lock check reads."""

pytestmark = [pytest.mark.integration, pytest.mark.requires_nix]


def evaluate(tree: Path, attribute: str) -> subprocess.CompletedProcess[str]:
    """Evaluate one attribute of the copied `nix/judge.nix`."""
    return subprocess.run(["nix-instantiate", "--eval", "--strict", "--json", str(tree / "nix/judge.nix"), "-A", attribute],
                          capture_output=True, text=True, timeout=NIX_TIMEOUT_SECONDS, check=False)


@pytest.fixture(scope="module")
def tree(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """A copy of the lock's inputs, claiming only corpus v1, with a lock of its current values."""
    copy = tmp_path_factory.mktemp("judge-lock")
    for relative in COPIED:
        source, target = ROOT / relative, copy / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        (shutil.copytree if source.is_dir() else shutil.copy2)(source, target)
    claims = {"corpora": {"corpus-v1": {"path": "conformance/corpus-v1", "mustAgree": [],
                                         "forbidden": ["DISAGREE", "HARNESS_ERROR"]}}}
    (copy / "judge/claims.json").write_text(json.dumps(claims))
    (copy / "nix/judge.lock.json").write_text("{}")
    current = evaluate(copy, "current")
    assert current.returncode == 0, current.stderr
    (copy / "nix/judge.lock.json").write_text(current.stdout)
    return copy


@pytest.mark.parametrize("relative,part", [
    ("conformance/corpus-v1/manifest.json", "corpus corpus-v1"),
    ("judge/claims.json", "judge"),
    ("judge/compare.py", "judge"),
    ("nix/sqlite.nix", "oracle"),
])
def test_a_changed_part_stops_evaluation(tree: Path, relative: str, part: str) -> None:
    """`nix/judge.nix` `locked`: one changed byte in a part stops evaluation and names the part;
    the restored part passes again."""
    assert evaluate(tree, "locked").returncode == 0
    path = tree / relative
    original = path.read_bytes()
    path.write_bytes(original + b" ")
    try:
        changed = evaluate(tree, "locked")
        assert changed.returncode != 0
        assert f"the judge changed: {part} differs from nix/judge.lock.json" in changed.stderr
    finally:
        path.write_bytes(original)
    assert evaluate(tree, "locked").returncode == 0


def test_an_unknown_lock_entry_stops_evaluation(tree: Path) -> None:
    """`nix/judge.nix` `locked`: a lock entry for a part that the claims no longer name is a change."""
    lock = tree / "nix/judge.lock.json"
    original = lock.read_text()
    lock.write_text(json.dumps({**json.loads(original), "corpus removed": "/nix/store/x"}))
    try:
        assert "corpus removed differs" in evaluate(tree, "locked").stderr
    finally:
        lock.write_text(original)
