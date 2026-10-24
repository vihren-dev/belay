"""Every `.lean` file of the repository is in exactly one build category (ADR 0010 section 7).

The category decides how a file is built: packages by their own Nix derivation,
direct fixtures by the test that uses them; excluded files are not built by CI. A
new Lean file outside all categories fails this test, so no Lean file is left
unbuilt without notice.
"""

from dataclasses import dataclass
from pathlib import Path

import pytest

pytestmark = pytest.mark.unit

ROOT = Path(__file__).resolve().parents[1]
"""Repository checkout."""

SKIPPED_DIRECTORIES = frozenset({".git", ".jj", ".lake", "build", "dist", "__pycache__"})
"""Generated or version-control trees; their Lean files are copies or outputs, not sources."""


@dataclass(frozen=True)
class Rules:
    """Path prefixes (relative, POSIX) of each category."""

    package: tuple[str, ...]
    direct_fixture: tuple[str, ...]
    excluded: tuple[str, ...]


REPOSITORY_RULES = Rules(
    package=("packages/",),
    direct_fixture=("tests/public_doc_inventory/", "tests/surface/", "tests/docgen/", "conformance/regressions/"),
    excluded=("experiments/",),
)
"""The categories of this repository."""


def lean_files(root: Path) -> list[str]:
    """Relative paths of the `.lean` source files under `root`, without generated trees or symbolic links."""
    found: list[str] = []
    pending = [root]
    while pending:
        directory = pending.pop()
        for entry in directory.iterdir():
            if entry.is_symlink() or entry.name in SKIPPED_DIRECTORIES:
                continue
            if entry.is_dir():
                pending.append(entry)
            elif entry.suffix == ".lean":
                found.append(entry.relative_to(root).as_posix())
    return sorted(found)


def categories(path: str, rules: Rules) -> list[str]:
    """The categories whose prefixes match one relative path; a correct tree gives exactly one."""
    matched = {"package": rules.package, "direct fixture": rules.direct_fixture, "excluded": rules.excluded}
    found = [name for name, prefixes in matched.items() if any(path.startswith(prefix) for prefix in prefixes)]
    return found


def problems(root: Path, rules: Rules) -> list[str]:
    """One message for each Lean file that is in no category or in more than one."""
    messages = []
    for path in lean_files(root):
        found = categories(path, rules)
        if len(found) != 1:
            where = ", ".join(found) if found else "no category"
            messages.append(f"{path}: {where}. Place the file in exactly one category of "
                            "ADR 0010 section 7, or add a rule in tests/test_lean_categories.py.")
    return messages


FIXTURE_RULES = Rules(package=("packages/",), direct_fixture=("fixtures/",), excluded=("scratch/",))
"""Rules for the small fixture trees below."""


def fixture_tree(root: Path, *files: str) -> Path:
    """Write empty files at the given relative paths."""
    for name in files:
        (root / name).parent.mkdir(parents=True, exist_ok=True)
        (root / name).write_text("")
    return root


def test_fixture_tree_in_categories(tmp_path: Path) -> None:
    """`problems` accepts a tree whose files are in packages, fixtures or excluded folders, and skips
    generated `.lake` trees."""
    root = fixture_tree(tmp_path, "packages/lib/Lib.lean", "fixtures/F.lean", "scratch/S.lean",
                        "packages/lib/.lake/build/Copy.lean")
    assert problems(root, FIXTURE_RULES) == []


def test_file_in_no_category_is_reported(tmp_path: Path) -> None:
    """`problems` names a Lean file that no rule covers, so it cannot escape the build of the cache."""
    root = fixture_tree(tmp_path, "loose/Loose.lean")
    assert problems(root, FIXTURE_RULES) == [
        "loose/Loose.lean: no category. Place the file in exactly one category of ADR 0010 section 7, "
        "or add a rule in tests/test_lean_categories.py."]


def test_file_in_two_categories_is_reported(tmp_path: Path) -> None:
    """`problems` names a Lean file that two rules cover, because its build would be ambiguous."""
    root = fixture_tree(tmp_path, "packages/lib/Lib.lean")
    rules = Rules(package=("packages/",), direct_fixture=("packages/lib/",), excluded=())
    assert problems(root, rules) == [
        "packages/lib/Lib.lean: package, direct fixture. Place the file in exactly one category of "
        "ADR 0010 section 7, or add a rule in tests/test_lean_categories.py."]


def test_repository_lean_files_are_each_in_one_category() -> None:
    """Every Lean source of this repository is in exactly one category."""
    assert lean_files(ROOT), "no Lean files found; the test is not looking at the repository"
    assert problems(ROOT, REPOSITORY_RULES) == []
