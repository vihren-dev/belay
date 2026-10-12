"""`migration_check.cache_location`: which Lake cache `prepare` and `verify-bundle` use, and its cleanup."""

from pathlib import Path

import pytest

from migration_check.cache_location import cache_directory, clean_other_versions, default_root, runtime_version

pytestmark = pytest.mark.unit


def test_explicit_option_wins_then_environment_then_default(tmp_path: Path) -> None:
    """`cache_directory` uses `--cache` first, then `BELAY_CACHE_DIR`, then the default root's version
    subfolder, so CI and tests can choose a cache and users get one per runtime build."""
    environment = {"BELAY_CACHE_DIR": str(tmp_path / "from-env")}
    assert cache_directory(tmp_path / "option", environment, tmp_path, "linux", "v1") == (tmp_path / "option").resolve()
    assert cache_directory(None, environment, tmp_path, "linux", "v1") == (tmp_path / "from-env").resolve()
    assert cache_directory(None, {}, tmp_path, "linux", "v1") == tmp_path / ".cache/belay/v1"


def test_default_root_follows_platform_conventions(tmp_path: Path) -> None:
    """`default_root` uses `XDG_CACHE_HOME` on Linux when set, and `~/Library/Caches` on macOS."""
    assert default_root({"XDG_CACHE_HOME": str(tmp_path / "xdg")}, tmp_path, "linux") == tmp_path / "xdg/belay"
    assert default_root({}, tmp_path, "darwin") == tmp_path / "Library/Caches/belay"


def test_clean_removes_only_other_versions(tmp_path: Path) -> None:
    """`clean_other_versions` keeps the current version's folder and plain files, and removes the rest."""
    for name in ("current", "old-1", "old-2"):
        (tmp_path / name).mkdir()
        (tmp_path / name / "entry").write_text("x")
    (tmp_path / "note.txt").write_text("kept")
    assert clean_other_versions(tmp_path, "current") == [tmp_path / "old-1", tmp_path / "old-2"]
    assert sorted(path.name for path in tmp_path.iterdir()) == ["current", "note.txt"]
    assert clean_other_versions(tmp_path / "absent", "current") == []


def test_runtime_version_changes_with_the_build(tmp_path: Path) -> None:
    """`runtime_version` differs for a different library path, so a new runtime build gets a fresh folder."""
    first = runtime_version(tmp_path / "lean", (tmp_path / "lib-a",))
    assert first == runtime_version(tmp_path / "lean", (tmp_path / "lib-a",)) and len(first) == 16
    assert first != runtime_version(tmp_path / "lean", (tmp_path / "lib-b",))
